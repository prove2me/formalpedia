-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum
-- name    : LanglandsTunnell.CubicInduction.dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/47b93843-aa15-5af8-bb2d-3bcc6007e9a1
-- title:
--   Local constancy, large-modulus vanishing and finite-sum dual Jacquet slices
-- statement:
--   Fix a nonzero prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, a triple $\nu = (\nu_0,\nu_1,\nu_2)$ of multiplicative characters $\nu_i : (\mathbb{Q}_v)^{\times} \to \mathbb{C}^{\times}$, each locally constant, and a locally constant, compactly supported $\Phi : \mathbb{Q}_v^3 \to \mathbb{C}$; the field $\mathbb{Q}_v =$ `v.adicCompletion ℚ` carries its Borel structure. For a unit $a$ and a point $x \in \mathbb{Q}_v$ put $g(a,x) = w_3 \cdot {}^{t}\!\big(\iota(\mathrm{diag}(a,1))\, u_{21}(x)\, (w' \cdot {}^{t}1^{-1})\big)^{-1} \cdot w_0$, where $w_3$ is the antidiagonal permutation matrix `longWeyl3`, $\iota$ the block embedding $GL_2 \hookrightarrow GL_3$ with $1$ in the last diagonal entry, $u_{21}(x)$ the lower unipotent matrix with entry $x$ in position $(2,1)$, $w'$ the permutation matrix interchanging the last two coordinates, $w_0 =$ `antidiagonal3 v`, and `transposeInv3` sends $h$ to ${}^{t}(h^{-1})$. Let $W(a,x)$ denote `jacquetValue v` — the truncated Jacquet integral at the level `jacquetLevel` — of the right translate by $g(a,x)$ of the big-cell section `cellSectionOf v ν Φ`, namely the indicator of `bigCell3 v` of $h \mapsto$ `cellValue v ν h` $\cdot\, \Phi($`cellRatio v h`$)$, and write $|a| =$ `modulus a` for the module of $a$ (the Haar character of multiplication by $a$). The assertion is a conjunction of four statements. (1) For every $x$ and every $F : \mathbb{Q}_v \to \mathbb{C}$ with $F(0) = 0$ and $F(a) = W(a,x)\,|a|^{-1}$ at all units $a$, and every $t \neq 0$, one has $F(t') = F(t)$ for all $t'$ in a neighbourhood of $t$. (2) The same local constancy away from $0$ holds for every $G : \mathbb{Q}_v \to \mathbb{C}$ with $G(0) = 0$ and $G(a) = \big(\int_{\mathbb{Q}_v} W(a,x)\,\mathrm{d}x\big)|a|^{-1}$ at units $a$, the integral being against the self-dual Haar measure `selfDualHaarAt ℚ v`. (3) There is a single real bound $B$ such that every $F$ as in (1), for every $x$, and every $G$ as in (2) vanish at each $t$ with $|t| > B$. (4) There are a finite set $S \subseteq \mathbb{Q}_v$ and a constant $c \in \mathbb{C}$ such that for every unit $a$, $\big(\int_{\mathbb{Q}_v} W(a,x)\,\mathrm{d}x\big)|a|^{-1} = c \sum_{x \in S} W(a,x)\,|a|^{-1}$.
--
--   These are the local regularity properties of the one-variable slices of the dual Jacquet (Whittaker) functional attached to a big-cell section of a principal series of $GL_3(\mathbb{Q}_v)$: local constancy on $\mathbb{Q}_v^{\times}$, vanishing for large module, and reduction of the $x$-integral to a finite sum of slices. They serve as the non-archimedean input for the analysis of the $GL_3 \times GL_1$ dual local zeta integral, being used in the proofs of the threefold twisted difference identity, of the Laurent expansion of the dual local zeta integral at $1-s$, and of its convergence in a right half-plane.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory

theorem LanglandsTunnell.CubicInduction.dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    letI := localBorel ℚ v
    (∀ x : v.adicCompletion ℚ, ∀ F : v.adicCompletion ℚ → ℂ, F 0 = 0 →
      (∀ a : (v.adicCompletion ℚ)ˣ,
        F a = jacquetValue v (gl3AmbientRightTranslate (R := ℂ)
            (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
              antidiagonal3 v)
            (cellSectionOf v ν Φ)) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹) →
      ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, F t' = F t) ∧
    (∀ G : v.adicCompletion ℚ → ℂ, G 0 = 0 →
      (∀ a : (v.adicCompletion ℚ)ˣ,
        G a = (∫ x : v.adicCompletion ℚ, jacquetValue v (gl3AmbientRightTranslate (R := ℂ)
              (longWeyl3 *
                  transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
                antidiagonal3 v)
            (cellSectionOf v ν Φ)) ∂(selfDualHaarAt ℚ v)) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹) →
      ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, G t' = G t) ∧
    (∃ B : ℝ,
      (∀ x : v.adicCompletion ℚ, ∀ F : v.adicCompletion ℚ → ℂ, F 0 = 0 →
        (∀ a : (v.adicCompletion ℚ)ˣ,
          F a = jacquetValue v (gl3AmbientRightTranslate (R := ℂ)
              (longWeyl3 *
                  transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
                antidiagonal3 v)
              (cellSectionOf v ν Φ)) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹) →
        ∀ t : v.adicCompletion ℚ, B < (modulus t : ℝ) → F t = 0) ∧
      (∀ G : v.adicCompletion ℚ → ℂ, G 0 = 0 →
        (∀ a : (v.adicCompletion ℚ)ˣ,
          G a = (∫ x : v.adicCompletion ℚ, jacquetValue v (gl3AmbientRightTranslate (R := ℂ)
                (longWeyl3 *
                    transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
                  antidiagonal3 v)
              (cellSectionOf v ν Φ)) ∂(selfDualHaarAt ℚ v)) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹) →
        ∀ t : v.adicCompletion ℚ, B < (modulus t : ℝ) → G t = 0)) ∧
    ∃ (S : Finset (v.adicCompletion ℚ)) (c : ℂ), ∀ a : (v.adicCompletion ℚ)ˣ,
      (∫ x : v.adicCompletion ℚ, jacquetValue v (gl3AmbientRightTranslate (R := ℂ)
            (longWeyl3 *
                transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
              antidiagonal3 v)
          (cellSectionOf v ν Φ)) ∂(selfDualHaarAt ℚ v)) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹ =
        c * (∑ x ∈ S,
          jacquetValue v (gl3AmbientRightTranslate (R := ℂ)
              (longWeyl3 *
                  transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
                antidiagonal3 v)
              (cellSectionOf v ν Φ)) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹) := by sorry
