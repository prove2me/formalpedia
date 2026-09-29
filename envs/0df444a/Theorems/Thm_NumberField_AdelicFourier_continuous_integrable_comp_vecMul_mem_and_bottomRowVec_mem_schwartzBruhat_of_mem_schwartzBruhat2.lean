-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
-- name    : NumberField.AdelicFourier.continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/514844f6-848d-5767-9c9c-7abfd375e2e2
-- title:
--   Basic properties of two-variable adelic Schwartz–Bruhat functions
-- statement:
--   Let $F$ be a number field, equipped with a measurable space structure on its adele ring $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F` that is the Borel structure of the topology, and let $\Phi\colon \mathbb{A}_F^2 \to \mathbb{C}$ (functions on `Fin 2 → AdeleRing (𝓞 F) F`) lie in `schwartzBruhat2 F`, the $\mathbb{C}$-linear span of the pure tensors $x \mapsto g\bigl((\mathrm{ringEquiv\_mixedSpace}\,F)(x_i)_\infty)_i\bigr)\cdot h\bigl(((x_i)_f)_i\bigr)$ with $g$ a Schwartz function on the two-fold product of the mixed space of $F$ and $h$ a locally constant, compactly supported function of the two finite-adelic coordinates. Then, simultaneously: $\Phi$ is continuous; for each $N \in \mathbb{N}$ there are $C \ge 0$ and a compact $K \subseteq (\mathbb{A}_{F,f})^2$ with $\|\Phi(x)\|\,(1+\|(x_{i,\infty})_i\|)^N \le C$ for all $x$, the norm being that of the pair of archimedean components in the mixed space, and $\Phi(x)=0$ whenever the pair of finite components is outside $K$; $\Phi$ is integrable for every additive Haar measure on $\mathbb{A}_F^2$, and in particular for `pairHaar μ₁`, the product of two copies of any additive Haar measure $\mu_1$ on $\mathbb{A}_F$; and `schwartzBruhat2 F` contains $x \mapsto \Phi(xg)$ for every $g \in \mathrm{GL}_2(\mathbb{A}_F)$ (row vector times matrix), $x \mapsto \Phi(tx)$ for every unit $t$ of $\mathbb{A}_F$, and $x \mapsto \Phi(x+a)$ for every $a \in \mathbb{A}_F^2$; finally, for every $g \in \mathrm{GL}_2(\mathbb{A}_F)$ the one-variable function $t \mapsto \Phi\bigl((t\,g_{1j})_j\bigr)$ lies in `schwartzBruhat F`.
--
--   This collects the standard regularity and stability properties of Weil's standard (Schwartz–Bruhat) functions, here for the two-variable adelic space carrying the Godement sections and the Godement–Eisenstein series on $\mathrm{GL}_2$. It is the basic input for the convergence and integrability statements about Godement sections and their zeta integrals, and for the $\mathrm{GL}_2(\mathbb{A}_F)$-equivariance of the construction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2.lean

import Definitions.Def_AutomorphicForm_GodementSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier IsDedekindDomain

open scoped Classical in

theorem NumberField.AdelicFourier.continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (hΦ : Φ ∈ schwartzBruhat2 F) :
    Continuous Φ ∧
    (∀ N : ℕ, ∃ (C : ℝ) (K : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F)), 0 ≤ C ∧ IsCompact K ∧
      (∀ x : Fin 2 → AdeleRing (𝓞 F) F,
        ‖Φ x‖ * (1 + ‖fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1‖) ^ N ≤ C) ∧
      (∀ x : Fin 2 → AdeleRing (𝓞 F) F, (fun i => (x i).2) ∉ K → Φ x = 0)) ∧
    (∀ (μ : Measure (Fin 2 → AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure], Integrable Φ μ) ∧
    (∀ (μ₁ : Measure (AdeleRing (𝓞 F) F)) [μ₁.IsAddHaarMeasure], Integrable Φ (pairHaar μ₁)) ∧
    (∀ g : AutomorphicForm.AdelicGL2 (𝓞 F) F,
      (fun x => Φ (Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))))
        ∈ schwartzBruhat2 F) ∧
    (∀ t : (AdeleRing (𝓞 F) F)ˣ, (fun x => Φ ((t : AdeleRing (𝓞 F) F) • x)) ∈ schwartzBruhat2 F) ∧
    (∀ a : Fin 2 → AdeleRing (𝓞 F) F, (fun x => Φ (x + a)) ∈ schwartzBruhat2 F) ∧
    (∀ g : AutomorphicForm.AdelicGL2 (𝓞 F) F,
      (fun t : AdeleRing (𝓞 F) F => Φ (AutomorphicForm.bottomRowVec F g t)) ∈ schwartzBruhat F) := by sorry
