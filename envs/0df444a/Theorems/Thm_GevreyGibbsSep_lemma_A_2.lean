-- Prove2me | Theorems.Thm_GevreyGibbsSep_lemma_A_2
-- name    : GevreyGibbsSep.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:36:46.265524+00:00
-- url     : https://prove2.me/theorems/3d41d3a0-8479-43ab-91bf-2a537ff68f75
-- title:
--   Lemma A.2 — $\mathrm{Gap}(\mathcal L^\dagger)\ge\beta^{-1}e^{-\beta\Delta}$
-- statement:
--   Let $E$ be a periodic potential, $\beta>0$, $p=e^{-\beta E}/Z$ and $\mathcal L^\dagger=-\nabla E\cdot\nabla+\beta^{-1}\Delta$. With $\langle f,g\rangle_p=\int_{\mathbb T^d}fg\,p\,dx$ and $\mathrm{Var}_p(f)=\|f-\int fp\|_p^2$, the spectral gap
--   $$\mathrm{Gap}(\mathcal L^\dagger)=\inf_{f\notin\ker\mathcal L^\dagger}\frac{\langle f,-\mathcal L^\dagger f\rangle_p}{\mathrm{Var}_p(f)}$$
--   satisfies $\mathrm{Gap}(\mathcal L^\dagger)\ge\beta^{-1}e^{-\beta\Delta}$, $\Delta=\max E-\min E$. Equivalently, for every smooth periodic $f$,
--   $$\beta^{-1}e^{-\beta\Delta}\,\mathrm{Var}_p(f)\ \le\ \langle f,-\mathcal L^\dagger f\rangle_p=\int_{\mathbb T^d}f\big(\nabla E\cdot\nabla f-\beta^{-1}\Delta f\big)p\,dx .$$
--
--   The gap controls the filtering threshold of the quantum algorithm.
--
--   **Formalization Note** $\Delta$ enters through any $D$ with $E(x)-E(y)\le D$ for all $x,y$; $D=\max E-\min E$ gives (A42).
--
--   Differences from the source:
--   - reading: $\mathrm{Gap}(\mathcal L^\dagger)\ge c$, an infimum of Rayleigh quotients over $f\notin\ker\mathcal L^\dagger$ → $c\,\mathrm{Var}_p(f)\le\langle f,-\mathcal L^\dagger f\rangle_p$ for every smooth periodic $f$; reason: kernel elements have $\mathrm{Var}_p(f)=0=\langle f,-\mathcal L^\dagger f\rangle_p$, and smooth periodic functions are a core of the form domain
--   - encoding: $\Delta=\max E-\min E$ → any $D$ with $E(x)-E(y)\le D$ for all $x,y$; reason: $D=\Delta$ is admissible and gives (A42); larger $D$ give weaker inequalities
--   - reading: $E:\mathbb T^d\to\mathbb R$ (regularity not stated) → $E$ $2\pi$-periodic and $C^\infty$; reason: $\mathcal L^\dagger$ needs $\nabla E$; the lemma is applied to potentials of the class, which are smooth
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Lemma A.2, Eqs. (A42)–(A44), p.25

import Mathlib
import Definitions.Def_GevreyGibbsSep_periodCube
import Definitions.Def_GevreyGibbsSep_IsPeriodicSmooth
import Definitions.Def_GevreyGibbsSep_iterPartial
import Definitions.Def_GevreyGibbsSep_partitionFn
import Definitions.Def_GevreyGibbsSep_grad

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- Lemma A.2 (lower bound on `Gap(L†)`), arXiv:2608.24527 (sha256 d4fd40eb…), Eqs. (A42)–(A44),
p.25. For `L† = −∇E·∇ + β^{−1}∆` and the Gibbs density `p = e^{−βE}/Z`,
`Gap(L†) = inf_{f ∉ ker L†} ⟨f, −L†f⟩_p / Var_p(f) ≥ β^{−1} e^{−β∆}`, `∆ = max E − min E`; stated
as the Poincaré inequality `β^{−1} e^{−β∆} Var_p(f) ≤ ⟨f, −L†f⟩_p` for every smooth periodic `f`,
with `⟨f, g⟩_p = ∫ f g p` (A43) and `Var_p(f) = ‖f − ∫ f p‖²_p`.

**Formalization Note** `∆` enters through any `Δ` with `E x − E y ≤ Δ` for all `x, y`; taking
`Δ = max E − min E` gives (A42), and a larger `Δ` gives a weaker inequality. `E` is taken smooth
and periodic (the source writes `E : T^d → ℝ`; `L†` needs `∇E`). -/
theorem lemma_A_2 {d : ℕ} (β : ℝ) (hβ : 0 < β) (E : (Fin d → ℝ) → ℝ) (hE : IsPeriodicSmooth E)
    (Δ : ℝ) (hΔ : ∀ x y, E x - E y ≤ Δ) (f : (Fin d → ℝ) → ℝ) (hf : IsPeriodicSmooth f) :
    let p : (Fin d → ℝ) → ℝ := fun x => Real.exp (- (β * E x)) / partitionFn (fun y => β * E y)
    let mean : ℝ := ∫ x in periodCube d, f x * p x
    β⁻¹ * Real.exp (- (β * Δ)) * ∫ x in periodCube d, (f x - mean) ^ 2 * p x
      ≤ ∫ x in periodCube d,
          f x * (∑ i, grad E x i * grad f x i - β⁻¹ * ∑ i, iterPartial [i, i] f x) * p x := by sorry

end GevreyGibbsSep
