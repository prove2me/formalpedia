-- Prove2me | Theorems.Thm_FourierSparseTesting1656_Uniform_proposition_3_8
-- name    : FourierSparseTesting1656.Uniform.proposition_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:33:43.032217+00:00
-- url     : https://prove2.me/theorems/f3dbea58-178b-4972-a63f-ef5f5aa2bd5d
-- title:
--   Proposition 3.8 — $\operatorname{dist}(f,F_s)\le 8p_H(f)$ for every subspace $H$
-- statement:
--   Let $f:\mathbb F_2^n\to\{-1,+1\}$ be Boolean, let $s\ge1$ be an integer, let $H\le\mathbb F_2^n$ be any subspace, and fix a complement $W$ of $H^\perp$. Let $p_H(f)$ be the rejection probability of the checks of Algorithm 1 (SpectrumTest) for this fixed $H$, over independent uniform shifts $a,r$. Then
--   $$\operatorname{dist}(f,F_s)\le8\,p_H(f).$$
--
--   There is no assumption on $p_H(f)$ and none on $H$: no randomness of $H$, no collision-free event, no particular dimension. This is what makes the bound applicable to the recovered function $\tilde f$ of Section 4, which depends on the subspace drawn.
--
--   Differences from the source:
--
--   - encoding: Boolean f : F₂ⁿ → {−1,+1} → bit function with false ↦ +1, true ↦ −1; reason: bijective encoding; same instances
--   - encoding: p_H(f) for a complement W of H^⊥ fixed in §2 → statement for every complement W; reason: the source fixes an arbitrary complement; the checks only depend on W through a relabeling of frequencies
--   - encoding: dist(f, F_s) = min over F_s → distToSet f (Fs n s), the infimum of the finite nonempty set of distances; reason: F_s contains the constants for s ≥ 1, so the infimum is the attained minimum
--   - encoding: F_k defined for k ≤ 2ⁿ → Fs n s defined by the same formula for every s; reason: for s ≥ 2ⁿ it is the class of all Boolean functions, equal to F_{2ⁿ}; the proposition is stated for every integer s ≥ 1
-- source:
--   Arijit Ghosh, Manmatha Roy, STOC 2027 submission #1656 (October 2026), p. 15, Proposition 3.8 (with p_H of p. 10 and the checks of Algorithm 1, p. 8); PDF SHA256 5374116f8d05176f80f62c5fdaaddae029e1f9e6af853c5a8e1873cb4e83a123

import Mathlib
import Definitions.Def_FourierSparseTesting1656_Uniform_Correction

set_option autoImplicit false
open FourierDimTesting102.Quantum
open Classical

namespace FourierSparseTesting1656.Uniform

/-- Proposition 3.8, p.15: for every Boolean `f`, every integer `s ≥ 1` and every subspace `H`
(with any fixed complement `W` of `H^⊥`), `dist(f, F_s) ≤ 8 p_H(f)`. -/
theorem proposition_3_8 {n : ℕ} (s : ℕ) (hs : 1 ≤ s) (H W : Submodule (ZMod 2) (V n))
    (hW : IsComplementOfPerp H W) (f : BoolFn n) :
    distToSet f (Fs n s) ≤ 8 * pH s H W f := by sorry

end FourierSparseTesting1656.Uniform
