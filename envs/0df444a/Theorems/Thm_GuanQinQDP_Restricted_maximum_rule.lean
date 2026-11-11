-- Prove2me | Theorems.Thm_GuanQinQDP_Restricted_maximum_rule
-- name    : GuanQinQDP.Restricted.maximum_rule
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:43:10.973242+00:00
-- url     : https://prove2.me/theorems/7f712da4-7bc4-4a0b-8a52-ae0ad0b394ca
-- title:
--   Theorem 4.1 — maximum rule for $\Delta^{\mathrm{PPT}(i)}_{A,i}$ and for Product, LOCC, SEP and PPT observers
-- statement:
--   Let $A=\bigotimes_{j=1}^nA_j$ with qubit channels $A_j:M_2\to M_2$, acting on arbitrary, possibly entangled, inputs. The channels are not assumed unital, entanglement breaking or highly private. Write $\Delta_j(\gamma)=\Delta^{\mathrm{ALL}}_{A_j}(\gamma)$ for the standalone profile of the $j$-th component. Then for every $\gamma\ge1$:
--
--   1. for every register $i\in[n]$,
--   $$\Delta^{\mathrm{PPT}(i)}_{A,i}(\gamma)=\Delta_i(\gamma);\qquad(10)$$
--   2. for $n\ge1$ and each $\mathcal M\in\{\mathrm{Product},\mathrm{LOCC},\mathrm{SEP},\mathrm{PPT}\}$,
--   $$\Delta^{\mathcal M}_{A}(\gamma)=\max_{i\in[n]}\Delta_i(\gamma).\qquad(11)$$
--
--   So against every observer up to PPT, the tensor product is exactly as private as its least private component, at every point of the privacy profile. This is the quantum form of the classical parallel-composition maximum rule. For every $\varepsilon$, the smallest $\delta$ for which $A$ is $(\varepsilon,\delta)$-QDP against these classes is $\max_j\Delta_j(e^\varepsilon)$.
--
--   Differences from the source:
--
--   - generalization: LOCC events: events of (finite-round) LOCC protocols → closure of the events of finite-round n-party LOCC protocols with arbitrary finite local memories (loccEvents); reason: contains every source event; the closure stays inside the closed PPT event set and contains the Product events, so the equality for it also gives the equality for the finite-round class, which lies between Product and the closure
--   - reading: Product: local POVMs with classical post-processing → post-processing may be randomized: events Σ_z f(z) ⊗_j P_{j,z_j} with 0 ≤ f ≤ 1; reason: randomized post-processing is classical post-processing; it gives the convex hull of the deterministic events and leaves every profile unchanged
--   - encoding: Δ^M_A(γ) = max_i Δ^M_{A,i}(γ) and max_i Δ_i(γ) → ⨆ i : Fin n (a finite supremum), with clause (11) stated for 0 < n; reason: [n] is nonempty in the source; for n ≥ 1 the supremum over Fin n is the maximum
--   - encoding: sup over neighboring pairs and events; standalone profile Δ_i → sSup of real sets (profileAt, standaloneProfile); reason: the sets are nonempty and bounded by acceptance probabilities in [0,1], so sSup is the supremum
--   - encoding: SEP: events of separable POVMs → effects M with M and I − M fully separable across the n output sites; reason: every event of a separable POVM has this form, and such M is an event of the separable POVM {M, I − M}
-- source:
--   Ji Guan, Yecheng Qin, Parallel Composition of Quantum Differential Privacy: The Role of Measurement Restrictions, STOC 2027 submission #1640 (October 2026), source.pdf SHA-256 da23c8347251683a16df4c61de3fa1604211cdbf34d757a7a45feb0efd54c694, Theorem 4.1, eqs. (10)–(11) (printed p. 18 / PDF p. 19), with the setting of §2.5 (printed p. 14 / PDF p. 15) and §4 (printed p. 18 / PDF p. 19)

import Definitions.Def_GuanQinQDP_Restricted_Model
import Definitions.Def_GuanQinQDP_Restricted_Measurements
open QAlgorithms WildeQIT.EntBreaking

namespace GuanQinQDP.Restricted

/-- Theorem 4.1 (Maximum rule under restricted measurements), Guan–Qin, STOC 2027 submission
#1640, printed p. 18 / PDF p. 19, equations (10)–(11). Let `A = ⨂_{j=1}^n A_j` with qubit
channels `A_j : M₂ → M₂`, acting on arbitrary, possibly entangled, inputs, and let `γ ≥ 1`.

(10) For every register `i`, `Δ^{PPT(i)}_{A,i}(γ) = Δ_i(γ)`, the standalone profile of `A_i`.

(11) For `n ≥ 1` and each `M ∈ {Product, LOCC, SEP, PPT}`, `Δ^M_A(γ) = max_{i ∈ [n]} Δ_i(γ)`. -/
theorem maximum_rule (n : ℕ)
    (A : Fin n → (Matrix Qubit Qubit ℂ →ₗ[ℂ] Matrix Qubit Qubit ℂ))
    (hA : ∀ j, IsQuantumChannel (A j)) (γ : ℝ) (hγ : 1 ≤ γ) :
    (∀ i : Fin n, profileAt (pptEventsAt i) (tensorChannel A) i γ = standaloneProfile (A i) γ) ∧
    (0 < n → ∀ c : MeasClass, c ≠ MeasClass.all →
      profile (eventSet n 2 c) (tensorChannel A) γ = ⨆ i : Fin n, standaloneProfile (A i) γ) := by sorry

end GuanQinQDP.Restricted
