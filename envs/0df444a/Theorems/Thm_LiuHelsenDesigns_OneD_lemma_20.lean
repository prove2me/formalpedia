-- Prove2me | Theorems.Thm_LiuHelsenDesigns_OneD_lemma_20
-- name    : LiuHelsenDesigns.OneD.lemma_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T11:05:57.539564+00:00
-- url     : https://prove2.me/theorems/f55ad5d3-0c62-46df-899f-ca8bf2a55558
-- title:
--   Lemma 20 — simultaneous subspace transport and dimension existence
-- statement:
--   Let V be a finite-dimensional binary vector space of dimension n. Two ordered pairs (U₁,S₁) and (U₂,S₂) with matching individual dimensions and matching intersection dimension are carried to each other by an invertible linear transformation. Moreover, for nonnegative integers r,s,j,
--
--   $$
--   \exists U,S:\ \dim U=r,\ \dim S=s,\ \dim(U\cap S)=j\quad\Longleftrightarrow\quad\max(0,r+s-n)\le j\le\min(r,s).
--   $$
--
--   Both the transport clause and the complete existence equivalence are included, also in dimension zero.
--
--   Differences from the source:
--   - encoding: max(0,r+s-n)≤j≤min(r,s) → r+s≤n+j and j≤r and j≤s for natural dimensions; reason: equivalent inequalities avoid truncated subtraction and retain the complete iff
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), p. 38, Lemma 20. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Mathlib

namespace LiuHelsenDesigns.OneD
theorem lemma_20 (V : Type) [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] :
    (∀ U₁ U₂ S₁ S₂ : Submodule (ZMod 2) V,
      Module.finrank (ZMod 2) U₁ = Module.finrank (ZMod 2) U₂ →
      Module.finrank (ZMod 2) S₁ = Module.finrank (ZMod 2) S₂ →
      Module.finrank (ZMod 2) ↥(U₁ ⊓ S₁) = Module.finrank (ZMod 2) ↥(U₂ ⊓ S₂) →
      ∃ G : V ≃ₗ[ZMod 2] V, U₁.map G.toLinearMap = U₂ ∧ S₁.map G.toLinearMap = S₂) ∧
    (∀ r s j : ℕ,
      (∃ U S : Submodule (ZMod 2) V,
        Module.finrank (ZMod 2) U = r ∧ Module.finrank (ZMod 2) S = s ∧
        Module.finrank (ZMod 2) ↥(U ⊓ S) = j) ↔
      r+s ≤ Module.finrank (ZMod 2) V+j ∧ j ≤ r ∧ j ≤ s) := by sorry
end LiuHelsenDesigns.OneD
