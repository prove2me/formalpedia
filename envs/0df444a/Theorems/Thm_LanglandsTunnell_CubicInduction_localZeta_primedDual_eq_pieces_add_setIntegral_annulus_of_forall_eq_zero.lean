-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero
-- name    : LanglandsTunnell.CubicInduction.localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/5c4e9534-222b-55dc-9111-eac67bd0d9cb
-- title:
--   Four-term decomposition of the dual local zeta integral
-- statement:
--   Fix a finite place $v$ of $\mathbb{Q}$ (a height-one prime of $\mathcal{O}_{\mathbb{Q}}$), write $F_v = \mathbb{Q}_v$ for the completion, and let $\nu_0,\nu_1,\nu_2 \colon F_v^{\times} \to \mathbb{C}^{\times}$ and $\chi \colon F_v^{\times} \to \mathbb{C}^{\times}$ be locally constant characters, $\Phi \colon F_v^3 \to \mathbb{C}$ locally constant with compact support, and assume $|(\nu_i\chi)(\varpi_v)| = 1$ for each $i$, where $\varpi_v$ is the chosen uniformiser unit. Let $s \in \mathbb{C}$ with $0 < \operatorname{Re} s < 1$. Put $g(a,x) = w_3 \cdot {}^{t}\!\big(\iota(\operatorname{diag}(a,1))\, u^{-}_{21}(x)\, (w'_3 \cdot {}^{t}\!1)\big)^{-1} \cdot w$, with $w_3$ the long Weyl element, $w'_3$ the transposition of the last two coordinates, $\iota$ the upper-left embedding $\mathrm{GL}_2 \hookrightarrow \mathrm{GL}_3$, $u^{-}_{21}(x)$ the lower unipotent matrix with entry $x$ in position $(2,1)$, and $w$ the antidiagonal permutation matrix; and let $f =$ `cellSectionOf v ν Φ` be the function on $\mathrm{GL}_3(F_v)$ supported on the big cell (where the corner entry and the lower minor are non-zero) whose value at $g$ is `cellValue v ν g` times $\Phi$ of the triple `cellRatio v g`. The data are: $F \colon F_v \to \mathbb{C}$ with $F(a) = |a|^{-1}\int_{F_v} \mathrm{Jac}\big(R_{g(a,x)}f\big)\,dx$ for every $a \in F_v^{\times}$, where $\mathrm{Jac}$ is the stabilised truncated Jacquet integral `jacquetValue` and $R$ is right translation, together with the hypothesis that $x \mapsto F(x)\,\chi^{-1}(x)\,|x|^{1-s}$ is integrable for the multiplicative measure $d^{\times}x = |x|^{-1}dx$ attached to the self-dual additive Haar measure; $K \colon \mathbb{Z} \to F_v \to F_v \to \mathbb{C}$ with $K_c(a,x)$, for $a \in F_v^{\times}$, the integral of $\psi_v(-(\alpha+\beta))\, f\big(w\, u_3(\alpha,\beta,\gamma)\, g(a,x)\big)$ over the truncation region $\{|\beta| \le q^{c},\ |\gamma| \le q^{c}|\beta|,\ |\alpha - \gamma/\beta| \le q^{c}\}$ against the product self-dual measure; $J$ with $J(a,x) = \mathrm{Jac}(R_{g(a,x)}f)$ for $a \in F_v^{\times}$; $G$ with $G_c(a) = |a|^{-1}\int_{F_v} K_c(a,x)\,dx$ for $a \in F_v^{\times}$; and natural numbers $N, R$ such that $J(a,x) = 0$ whenever $a \in F_v^{\times}$ and $|x| > q^{R}$. Then for every $c \in \mathbb{Z}$ the Tate local zeta integral $\int G_c(a)\,\chi^{-1}(a)\,|a|^{1-s}\,d^{\times}a$ equals the sum of four terms: the integral over the annulus $\{q^{-N} \le |a| \le q^{N}\}$ of $|a|^{-1}\chi^{-1}(a)|a|^{1-s}\int_{|x| \le q^{R}} (K_c(a,x) - J(a,x))\,dx$; the same integral over the annulus with $\int_{|x| > q^{R}} K_c(a,x)\,dx$ in place of the inner integral; the integral over the complement of the annulus of $|a|^{-1}\chi^{-1}(a)|a|^{1-s}\int_{F_v} K_c(a,x)\,dx$; and $\int_{q^{-N} \le |a| \le q^{N}} F(a)\,\chi^{-1}(a)\,|a|^{1-s}\,d^{\times}a$. Here $|\cdot|$ is the normalised absolute value `modulus`, and characters are extended to all of $F_v$ by $0$ at $0$ via `charExt`.
--
--   This is the bookkeeping decomposition underlying the passage from the truncated Jacquet–Whittaker integrals at level $c$ to their limit in the local functional equation for the $\mathrm{GL}_3$ zeta integral of a big-cell section of a principal series: the difference between the level-$c$ kernel $K_c$ and the stabilised kernel $J$ is isolated on a compact annulus in $a$ and a ball in $x$, and the remaining contributions are collected in two tail terms. It is used to prove the convergence statement `tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal

theorem LanglandsTunnell.CubicInduction.localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1)
    (F : v.adicCompletion ℚ → ℂ)
    (hF : ∀ a : (v.adicCompletion ℚ)ˣ,
      letI := localBorel ℚ v
      F a =
        (∫ x : v.adicCompletion ℚ,
            jacquetValue v (gl3AmbientRightTranslate (R := ℂ)
              (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x *
                (weylPrime3 * transposeInv3 1)) * antidiagonal3 v) (cellSectionOf v ν Φ))
          ∂(selfDualHaarAt ℚ v)) *
          ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹)
    (hint :
      letI := localBorel ℚ v
      Integrable (fun x => F x * charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s))
        (mulMeasure (selfDualHaarAt ℚ v)))
    (K : ℤ → v.adicCompletion ℚ → v.adicCompletion ℚ → ℂ)
    (hK : ∀ (c : ℤ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      letI := localBorel ℚ v
      K c a x =
        ∫ p in {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
            Valued.v p.2.1 ≤ WithZero.exp c ∧ Valued.v p.2.2 ≤ WithZero.exp c * Valued.v p.2.1 ∧
              Valued.v (p.1 - p.2.2 / p.2.1) ≤ WithZero.exp c},
          (psiLocal ℚ v (-(p.1 + p.2.1)) : ℂ) *
            cellSectionOf v ν Φ
              (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 *
                (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x *
                  (weylPrime3 * transposeInv3 1)) * antidiagonal3 v))
          ∂(jacquetHaar3 v))
    (J : v.adicCompletion ℚ → v.adicCompletion ℚ → ℂ)
    (hJ : ∀ (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      J a x =
        jacquetValue v (gl3AmbientRightTranslate (R := ℂ)
          (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x *
            (weylPrime3 * transposeInv3 1)) * antidiagonal3 v) (cellSectionOf v ν Φ)))
    (G : ℤ → v.adicCompletion ℚ → ℂ)
    (hG : ∀ (c : ℤ) (a : (v.adicCompletion ℚ)ˣ),
      letI := localBorel ℚ v
      G c a =
        (∫ x : v.adicCompletion ℚ, K c a x ∂(selfDualHaarAt ℚ v)) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹)
    (N R : ℕ)
    (hR : ∀ (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ), WithZero.exp (R : ℤ) < Valued.v x →
      J (a : v.adicCompletion ℚ) x = 0)
    (c : ℤ) :
    letI := localBorel ℚ v
    localZeta (selfDualHaarAt ℚ v) (G c) χ⁻¹ (1 - s) =
      (∫ a in {t : v.adicCompletion ℚ | WithZero.exp (-(N : ℤ)) ≤ Valued.v t ∧ Valued.v t ≤ WithZero.exp (N : ℤ)},
          ((modulus a : ℝ) : ℂ)⁻¹ * charExt χ⁻¹ a * ((modulus a : ℝ) : ℂ) ^ (1 - s) *
            ∫ x in {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (R : ℤ)}, (K c a x - J a x)
              ∂(selfDualHaarAt ℚ v)
          ∂(mulMeasure (selfDualHaarAt ℚ v))) +
        (∫ a in {t : v.adicCompletion ℚ | WithZero.exp (-(N : ℤ)) ≤ Valued.v t ∧ Valued.v t ≤ WithZero.exp (N : ℤ)},
            ((modulus a : ℝ) : ℂ)⁻¹ * charExt χ⁻¹ a * ((modulus a : ℝ) : ℂ) ^ (1 - s) *
              ∫ x in {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (R : ℤ)}ᶜ, K c a x ∂(selfDualHaarAt ℚ v)
            ∂(mulMeasure (selfDualHaarAt ℚ v))) +
        (∫ a in {t : v.adicCompletion ℚ |
              WithZero.exp (-(N : ℤ)) ≤ Valued.v t ∧ Valued.v t ≤ WithZero.exp (N : ℤ)}ᶜ,
            ((modulus a : ℝ) : ℂ)⁻¹ * charExt χ⁻¹ a * ((modulus a : ℝ) : ℂ) ^ (1 - s) *
              ∫ x, K c a x ∂(selfDualHaarAt ℚ v) ∂(mulMeasure (selfDualHaarAt ℚ v))) +
        (∫ a in {t : v.adicCompletion ℚ | WithZero.exp (-(N : ℤ)) ≤ Valued.v t ∧ Valued.v t ≤ WithZero.exp (N : ℤ)},
          F a * charExt χ⁻¹ a * ((modulus a : ℝ) : ℂ) ^ (1 - s) ∂(mulMeasure (selfDualHaarAt ℚ v))) := by sorry
