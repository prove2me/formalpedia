-- Prove2me | Theorems.Thm_LiuHelsenDesigns_OneD_lemma_5
-- name    : LiuHelsenDesigns.OneD.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T11:07:38.97037+00:00
-- url     : https://prove2.me/theorems/f5a9f8e0-68a3-45cb-b068-bd74c0f96ab9
-- title:
--   Lemma 5 — Hadad abelian-extension bound
-- statement:
--   Consider an exact extension $1\to A\to\Gamma\to H\to1$ with A finite abelian and H finite (so Γ is finite, as Definition 5 requires of every group with an average Kazhdan constant). Let S and B be nonempty finite subsets of H and A, and choose any lift of S into Γ. Let B̃ be the union of the conjugation orbits of B. If κ_H and κ_A are average squared-displacement lower bounds in [0,4] for (H,S) and (A,B̃), then
--
--   $$
--   K_{av}(\Gamma;\widetilde S\cup B)\ge\frac{\kappa_H\kappa_A}{512(1+|S|/|B|+|B|/|S|)}.
--   $$
--
--   Only B is added to the lifted set; its full orbit is used to check kernel expansion.
--
--   Differences from the source:
--   - encoding: numerical Kazhdan constants and their inequalities → transport of every nonnegative lower bound over all Hilbert representations; reason: this expresses the full bound without an empty real infimum; finite-group averages agree with the irreducible-representation definition
--   - encoding: the numerical average Kazhdan constants of Definition 5 → the supplied lower bounds satisfy 0 ≤ κ_H,κ_A ≤ 4, including at trivial factors; reason: squared displacement of a unit vector by a unitary is at most 4; every defined finite-group source constant is in this range; without the upper caps the lower-bound predicate at a trivial factor is vacuous and permits false conclusions (Γ=A=Z/2, H=1, S={1}, B={a}, κ_A=4, κ_H=4096 gives 32/3 > 4)
--   - encoding: ratios |S|/|B| and |B|/|S| and averages over S and B → S and B nonempty; reason: the source expression is undefined otherwise; only undefined cases are excluded
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), p. 13, Lemma 5. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Definitions.Def_LiuHelsenDesigns_OneD_kazhdanBounds

universe u5

namespace LiuHelsenDesigns.OneD
attribute [local instance] Classical.decEq
theorem lemma_5 (A Γ H : Type u5) [CommGroup A] [Group Γ] [Group H] [Fintype A] [Finite H]
    (i : A →* Γ) (q : Γ →* H) (hi : Function.Injective i)
    (hq : Function.Surjective q) (hexact : i.range = q.ker)
    (S : Finset H) (B : Finset A) (hS : S.Nonempty) (hB : B.Nonempty)
    (lift : H → Γ) (hlift : ∀ s ∈ S, q (lift s) = s)
    (κH κA : ℝ) (hκH : 0 ≤ κH) (hκA : 0 ≤ κA)
    (hκH_max : κH ≤ 4) (hκA_max : κA ≤ 4)
    (hH : AverageKazhdanLower H S κH)
    (hA : AverageKazhdanLower A (kernelOrbit i B) κA) :
    AverageKazhdanLower Γ
      (S.image lift ∪ B.image i)
      (κH * κA / (512 * (1 + (S.card : ℝ)/B.card + (B.card : ℝ)/S.card))) := by sorry
end LiuHelsenDesigns.OneD
