-- Prove2me | Theorems.Thm_LiuHelsenDesigns_OneD_lemma_11
-- name    : LiuHelsenDesigns.OneD.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T11:10:43.761569+00:00
-- url     : https://prove2.me/theorems/aad4e3fe-9427-47c3-8df7-e7cf754998e1
-- title:
--   Lemma 11 — nearest-neighbor permutation expanders
-- statement:
--   There are positive constants c₀ and Δ, and a depth D, all independent of qubit count n and moment order k. An effective program returns nearest-neighbor NOT/CNOT/Toffoli circuits implementing a nonempty finite generating set S for the alternating group on the n-qubit basis. Whenever $k\le c_0 2^{n/6.1}$,
--
--   $$
--   \left\|\frac1{|S|}\sum_{\pi\in S}P(\pi)^{\otimes k}-\mathbb E_{\pi\in\operatorname{Alt}(2^n)}P(\pi)^{\otimes k}\right\|_{2\to2}\le1-\Delta.
--   $$
--
--   Every output circuit has depth at most D, for every n≥1, in a fixed open-chain layout.
--
--   Differences from the source:
--   - encoding: uniform O(·) and Ω(1) statements → positive constants chosen before every size, order, precision and representation they are uniform over; reason: only Theorem 1 constants and its size threshold may depend on the fixed c
--   - encoding: explicit sampling and finite gate implementation → a halting partial-recursive program returning encoded finite circuit lists, with real errors selecting ceiling binary precision; reason: uniform lists can include multiplicities; no polynomial classical runtime is asserted
--   - generalization: an explicit set S of NOT/CNOT/Toffoli products with g(µ(S),τ,Alt(2^ℓ)) = 1−Ω(1) → S is contained in Alt(2^n) and generates Alt(2^n), besides the gap; reason: S is Kassabov's generating set for the alternating group (pp.29–30, Eq. (174)), and g(µ(S),τ,Alt) presupposes a law on Alt; the Lean conclusion contains the source's
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), p. 29, Lemma 11. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Definitions.Def_LiuHelsenDesigns_OneD_localLaws

namespace LiuHelsenDesigns.OneD
theorem lemma_11 : ∃ (code : Nat.Partrec.Code) (c₀ Δ : ℝ) (D : ℕ),
    0 < c₀ ∧ 0 < Δ ∧ Δ ≤ 1 ∧
    ∀ n : ℕ, 1 ≤ n → ∃ cs : List Circuit, ∃ S : Finset (Equiv.Perm (Basis n)),
      ProgramOutputs code n 0 0 cs ∧ S.Nonempty ∧ ImplementsPermSet cs S ∧
      (∀ C ∈ cs, depth C ≤ D) ∧
      (S : Set (Equiv.Perm (Basis n))) ⊆ alternatingGroup (Basis n) ∧
      Subgroup.closure (S : Set (Equiv.Perm (Basis n))) = alternatingGroup (Basis n) ∧
      ∀ k : ℕ, (k : ℝ) ≤ c₀ * Real.rpow 2 ((n : ℝ)/6.1) →
        permutationEssential S k ≤ 1-Δ := by sorry
end LiuHelsenDesigns.OneD
