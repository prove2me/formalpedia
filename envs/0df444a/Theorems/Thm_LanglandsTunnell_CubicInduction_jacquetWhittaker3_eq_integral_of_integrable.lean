-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetWhittaker3_eq_integral_of_integrable
-- name    : LanglandsTunnell.CubicInduction.jacquetWhittaker3_eq_integral_of_integrable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/cb3f9f19-494c-52cc-a473-c257f4b59895
-- title:
--   Jacquet–Whittaker function as an absolutely convergent Jacquet integral
-- statement:
--   Let $v$ be a finite place of $\mathbb{Q}$, i.e. a height-one prime of $\mathcal{O}_{\mathbb{Q}}$, and write $F = \mathbb{Q}_v$ for the completion `v.adicCompletion ℚ`, equipped with its Borel $\sigma$-algebra `localBorel`. Let $\nu = (\nu_0,\nu_1,\nu_2)$ be a triple of group homomorphisms $F^\times \to \mathbb{C}^\times$, each locally constant, and let $\Phi : F^3 \to \mathbb{C}$ be locally constant with compact support. Let $g \in \mathrm{GL}_3(F)$. Let `cellSectionOf v ν Φ` be the function on $\mathrm{GL}_3(F)$ supported on the big cell $\{h : \mathrm{corner}(h) \neq 0,\ \mathrm{lowerMinor}(h) \neq 0\}$ and given there by $\mathrm{charExt}(\nu_0)(\det h/\mathrm{lowerMinor}(h)) \cdot \mathrm{charExt}(\nu_1)(\mathrm{lowerMinor}(h)/\mathrm{corner}(h)) \cdot \mathrm{charExt}(\nu_2)(\mathrm{corner}(h)) \cdot \bigl(\|\det h/\mathrm{lowerMinor}(h)\|/\|\mathrm{corner}(h)\|\bigr)$ times $\Phi$ evaluated at the triple $(h_{21}/\mathrm{corner}(h),\ h_{22}/\mathrm{corner}(h),\ \mathrm{outerMinor}(h)/\mathrm{lowerMinor}(h))$. Write $w_0$ for `antidiagonal3 v`, the antidiagonal permutation matrix, and $n(x,y,z)$ for `upperUnipotent3`, the upper triangular unipotent matrix with entries $x$, $y$ above the diagonal and $z$ in the corner. Assume that $(x,y,z) \mapsto \mathrm{cellSection}(w_0\, n(x,y,z)\, g)$ is integrable against `jacquetHaar3 v`, the threefold product of the self-dual Haar measure `selfDualHaarAt ℚ v` on $F$. Then `jacquetWhittaker3 v ν Φ g`, the value of the functional `jacquetValue` (a truncated Jacquet integral at the level `jacquetLevel` of the integrand) applied to the right translate $h \mapsto \mathrm{cellSection}(hg)$, equals $$\int_{F^3} \psi_v\bigl(-(x+y)\bigr)\, \mathrm{cellSection}\bigl(w_0\, n(x,y,z)\, g\bigr)\, d(x,y,z),$$ where $\psi_v =$ `psiLocal ℚ v` is the local component at $v$ of the standard additive character of the adeles of $\mathbb{Q}$.
--
--   This identifies the regularised (stabilised truncated) Jacquet functional attached to a cell section of the $\mathrm{GL}_3$ principal series with the classical Jacquet integral, at any $g$ where the latter converges absolutely. It is used by [`LanglandsTunnell.CubicInduction.integrable_and_jacquetWhittaker3_eq_integral_of_norm_eq_rpow_of_lt`](thm.html#LanglandsTunnell.CubicInduction.integrable_and_jacquetWhittaker3_eq_integral_of_norm_eq_rpow_of_lt), where absolute convergence is established in the relevant chamber of exponents.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_jacquetWhittaker3_eq_integral_of_integrable.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal

theorem LanglandsTunnell.CubicInduction.jacquetWhittaker3_eq_integral_of_integrable
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (g : LocalGL3 v)
    (hint : letI := localBorel ℚ v
      Integrable (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        cellSectionOf v ν Φ (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 * g)) (jacquetHaar3 v)) :
    letI := localBorel ℚ v
    jacquetWhittaker3 v ν Φ g =
      ∫ p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ,
        psiLocal ℚ v (-(p.1 + p.2.1)) *
          cellSectionOf v ν Φ (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 * g) ∂(jacquetHaar3 v) := by sorry
