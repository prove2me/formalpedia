-- Prove2me | Theorems.Thm_Kyprianou_Ch02_markedCompoundPoissonBoundedDisjointLawV6
-- name    : Kyprianou.Ch02.markedCompoundPoissonBoundedDisjointLawV6
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T11:46:28.501971+00:00
-- url     : https://prove2.me/theorems/487b22b9-5fa9-43d1-9bcf-73f9885f197b
-- title:
--   Bounded-window finite-disjoint Poisson law for marked compound Poisson arrivals
-- statement:
--   Let $(\Omega, \mathcal{F}, P)$ be a probability space carrying a Poisson counting process $N = (N_t)_{t \ge 0}$ of rate $\lambda > 0$ (as a Lévy process with $N_t \sim \mathrm{Poisson}(\lambda t)$), measurable arrival times $(T_n)_{n \ge 1}$ linked a.s. by $n \le N_t \iff T_n \le t$, and measurable i.i.d. marks $(\xi_k)_{k \ge 0}$ with common probability law $F$ on $\mathbb{R}$ satisfying $F(\{0\}) = 0$, independent of $(N_t)_{t \ge 0}$.
--
--   Define the marked arrival counting measure and intensity measure on $\mathbb{R} \times \mathbb{R}$ by
--
--   $$\mu_\omega := \sum_{n=0}^{\infty} \delta_{(T_{n+1}(\omega),\, \xi_{n+1}(\omega))}, \qquad \mathrm{intensity} := \big(\mathrm{Leb}|_{[0,\infty)}\big) \otimes (\lambda F).$$
--
--   Then for every time horizon $t \in [0,\infty)$ and every finite pairwise-disjoint measurable family $A_0, \dots, A_{m-1} \subseteq (0, t] \times \mathbb{R}$:
--
--   1. Each count $\omega \mapsto \mu_\omega(A_i)$ has the $\mathrm{Poisson}(\mathrm{intensity}(A_i))$ distribution pushed forward along $\mathbb{N} \hookrightarrow [0,\infty]$.
--   2. The random variables $(\omega \mapsto \mu_\omega(A_i))_{i < m}$ are mutually independent under $P$.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, Chapter 2, Section 2.1-2.2, pp. 33-39 (marked compound Poisson random measure on bounded time windows)

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

theorem markedCompoundPoissonBoundedDisjointLawV6
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hFzero : F {0} = 0)
    (N : ℝ≥0 → Ω → ℕ)
    (T : ℕ → Ω → ℝ≥0)
    (ξ : ℕ → Ω → ℝ)
    (hTmeas : ∀ n : ℕ, 0 < n → Measurable (T n))
    (hξmeas : ∀ k : ℕ, Measurable (ξ k))
    (hNlevy : ProbabilityTheory.IsLevyProcess
       (fun t ω => (N t ω : ℝ)) P)
    (hNlaw : ∀ t : ℝ≥0,
       P.map (N t) = ProbabilityTheory.poissonMeasure (rate * t))
    (harrival : ∀ᵐ ω ∂P,
       ∀ (n : ℕ), 0 < n →
         ∀ (t : ℝ≥0), (n ≤ N t ω ↔ T n ω ≤ t))
    (hmarklaw : ∀ k : ℕ, P.map (ξ k) = F)
    (hIID : ProbabilityTheory.iIndepFun ξ P)
    (hcross : ProbabilityTheory.Indep
      (⨆ k : ℕ, MeasurableSpace.comap (ξ k) inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (N t) inferInstance) P)
    (t : ℝ≥0) (m : ℕ) (A : Fin m → Set (ℝ × ℝ))
    (hAmeas : ∀ i, MeasurableSet (A i))
    (hAsub : ∀ i, A i ⊆ Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ)
    (hAdisj : Pairwise (fun i j => Disjoint (A i) (A j))) :
    let μ : Ω → Measure (ℝ × ℝ) := fun ω =>
      Measure.sum (fun n : ℕ =>
        Measure.dirac ((T (n + 1) ω : ℝ), ξ (n + 1) ω))
    let intensity : Measure (ℝ × ℝ) :=
      (volume.restrict (Set.Ici (0 : ℝ))).prod ((rate : ENNReal) • F)
    (∀ i : Fin m,
       P.map (fun ω => μ ω (A i)) =
         (ProbabilityTheory.poissonMeasure (intensity (A i)).toNNReal).map
           (Nat.cast : ℕ → ENNReal)) ∧
    ProbabilityTheory.iIndepFun (fun i (ω : Ω) => μ ω (A i)) P
    := by sorry

end Kyprianou.Ch02
