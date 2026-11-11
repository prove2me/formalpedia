-- Prove2me | Theorems.Thm_LiuHelsenDesigns_OneD_lemma_12
-- name    : LiuHelsenDesigns.OneD.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T11:11:10.786191+00:00
-- url     : https://prove2.me/theorems/1a36fdcf-39cf-40ee-b093-e8b4b7c227d4
-- title:
--   Lemma 12 — representation-uniform local Clifford gap
-- statement:
--   An effective program produces, for every $n\ge1$, a symmetric Clifford generating set S of uniformly bounded size at most 451 and uniform constant nearest-neighbor depth. A positive Δ independent of n and of every finite-dimensional unitary representation ρ without invariant vectors satisfies
--
--   $$
--   \left\|\frac1{|S\cup\{I\}|}\sum_{g\in S\cup\{I\}}\rho(g)\right\|_{2\to2}\le1-\Delta.
--   $$
--
--   The invariant projector is zero on the stated representation domain. The uniform average uses the actual set with identity adjoined.
--
--   Differences from the source:
--   - encoding: uniform O(·) and Ω(1) statements → positive constants chosen before every size, order, precision and representation they are uniform over; reason: only Theorem 1 constants and its size threshold may depend on the fixed c
--   - encoding: explicit sampling and finite gate implementation → a halting partial-recursive program returning encoded finite circuit lists, with real errors selecting ceiling binary precision; reason: uniform lists can include multiplicities; no polynomial classical runtime is asserted
--   - encoding: essential norm with the invariant projector subtracted → operator norm of the average on representations with no invariant vectors; reason: the invariant projector is zero on exactly the source representation domain
--   - generalization: a constant-size symmetric generating set → a symmetric generating set of size at most M with M ≤ 451; reason: Theorem 4 (p.6), which Lemmas 12 and 23 restate, bounds the set by 451; a fixed bound M ≤ 451 is in particular a constant size
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), p. 29, Lemma 12. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Definitions.Def_LiuHelsenDesigns_OneD_localLaws

namespace LiuHelsenDesigns.OneD
theorem lemma_12 : ∃ (code : Nat.Partrec.Code) (Δ : ℝ) (D M : ℕ),
    0 < Δ ∧ Δ ≤ 1 ∧ M ≤ 451 ∧
    ∀ n : ℕ, 1 ≤ n → ∃ cs : List Circuit, ∃ S : Finset (Cl n),
      ProgramOutputs code n 0 0 cs ∧ ImplementsClSet cs S ∧ S.card ≤ M ∧
      InverseClosed (S : Set (Cl n)) ∧ Subgroup.closure (S : Set (Cl n)) = ⊤ ∧
      (∀ C ∈ cs, depth C ≤ D) ∧
      ∀ d : ℕ, ∀ ρ : Cl n →* Matrix.unitaryGroup (Fin d) ℂ,
        NoInvariant ρ → clRepresentationNorm S ρ ≤ 1-Δ := by sorry
end LiuHelsenDesigns.OneD
