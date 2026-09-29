-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_norm_dualZetaRemainder_outside_annulus_le
-- name    : LanglandsTunnell.CubicInduction.exists_forall_norm_dualZetaRemainder_outside_annulus_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/c6feb032-6e0b-59b8-8d84-c04505b3cd60
-- title:
--   Uniform tail bound outside an annulus for the dual cubic zeta integral
-- statement:
--   Let $v$ be a finite place of $\mathbb{Q}$ (a height-one prime of $\mathcal{O}_{\mathbb{Q}}$), with completion $\mathbb{Q}_v$ carrying its Borel structure and the self-dual additive Haar measure $dt$ (the Haar measure giving the valuation ring volume $1$, scaled by $q^{-n(\psi_v)/2}$). Let $\nu_0,\nu_1,\nu_2$ and $\chi$ be locally constant homomorphisms $\mathbb{Q}_v^\times \to \mathbb{C}^\times$, let $\Phi : \mathbb{Q}_v^3 \to \mathbb{C}$ be locally constant with compact support, assume $|(\nu_i\chi)(\varpi_v)| = 1$ for each $i$, where $\varpi_v$ is the chosen uniformiser, and let $s \in \mathbb{C}$ with $0 < \mathrm{Re}\,s < 1$. Let $K : \mathbb{Z} \times \mathbb{Q}_v \times \mathbb{Q}_v \to \mathbb{C}$ satisfy, for every $c \in \mathbb{Z}$, every unit $a$ and every $x \in \mathbb{Q}_v$,
--   $$K_c(a,x) = \int \psi_v(-(\alpha+\beta))\, f_{\nu,\Phi}\big(J\, u(\alpha,\beta,\gamma)\, w\, (\iota(\mathrm{diag}(a,1))\,\ell(x)\,(w'\,{}^{t}1^{-1}))^{-\mathsf{T}} J\big)\, d\alpha\,d\beta\,d\gamma,$$
--   the integral being over $\{|\beta| \le q^{c},\ |\gamma| \le q^{c}|\beta|,\ |\alpha - \gamma/\beta| \le q^{c}\}$ against the triple self-dual Haar measure; here $J$ and $w$ are the antidiagonal permutation matrix, $w'$ the permutation interchanging the last two coordinates, $u(\alpha,\beta,\gamma)$ the upper unipotent matrix with entries $\alpha,\beta,\gamma$, $\iota$ the upper-left $GL_2 \hookrightarrow GL_3$ embedding, $\ell(x)$ the lower unipotent matrix with entry $x$ in position $(2,1)$, and $f_{\nu,\Phi}$ the big-cell section: the indicator of $\{$corner entry $\neq 0$, lower minor $\neq 0\}$ times $\mathrm{cellValue}_\nu \cdot \Phi(\mathrm{cellRatio})$. Then there is a sequence $\rho : \mathbb{N} \to \mathbb{R}$ tending to $0$ such that for all $N \in \mathbb{N}$ and all $c \in \mathbb{Z}$,
--   $$\Big\| \int_{\{q^{-N} \le |a| \le q^{N}\}^{c}} |a|^{-1}\, \chi^{-1}(a)\, |a|^{1-s} \Big(\int_{\mathbb{Q}_v} K_c(a,x)\, dx\Big)\, d^\times a \Big\| \le \rho(N),$$
--   where $|a|$ is the module $\mathrm{modulus}(a)$, $\chi^{-1}$ is extended by $0$ to $\mathbb{Q}_v$, and $d^\times a$ is the self-dual measure restricted to $\mathbb{Q}_v \setminus \{0\}$ with density $|a|^{-1}$. The bound is uniform in the truncation parameter $c$.
--
--   This is the tail estimate for the dual (Whittaker-side) local zeta integral of the cubic induction: the contribution of torus elements outside the annulus $q^{-N} \le |a| \le q^{N}$ is bounded by a null sequence independent of the Jacquet truncation level $c$. It supplies the uniformity needed to interchange the limit in $c$ with the integral over $\mathbb{Q}_v^\times$, and is used in [`LanglandsTunnell.CubicInduction.tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue`](thm.html#LanglandsTunnell.CubicInduction.tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_norm_dualZetaRemainder_outside_annulus_le.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal

theorem LanglandsTunnell.CubicInduction.exists_forall_norm_dualZetaRemainder_outside_annulus_le
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1)
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
          ∂(jacquetHaar3 v)) :
    letI := localBorel ℚ v
    ∃ ρ : ℕ → ℝ, Filter.Tendsto ρ Filter.atTop (nhds 0) ∧
      ∀ (N : ℕ) (c : ℤ),
        ‖∫ a in {t : v.adicCompletion ℚ |
              WithZero.exp (-(N : ℤ)) ≤ Valued.v t ∧ Valued.v t ≤ WithZero.exp (N : ℤ)}ᶜ,
            ((modulus a : ℝ) : ℂ)⁻¹ * charExt χ⁻¹ a * ((modulus a : ℝ) : ℂ) ^ (1 - s) *
              ∫ x, K c a x ∂(selfDualHaarAt ℚ v) ∂(mulMeasure (selfDualHaarAt ℚ v))‖ ≤ ρ N := by sorry
