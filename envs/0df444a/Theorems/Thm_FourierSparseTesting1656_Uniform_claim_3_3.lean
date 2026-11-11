-- Prove2me | Theorems.Thm_FourierSparseTesting1656_Uniform_claim_3_3
-- name    : FourierSparseTesting1656.Uniform.claim_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:33:32.025732+00:00
-- url     : https://prove2.me/theorems/c1357709-6e4c-4217-a1b3-89b54d3aaf9e
-- title:
--   Claim 3.3 — the corrected spectrum is the strict-majority vote at every coset
-- statement:
--   **Standing setup (§3.2, p.10).** Let $n\ge0$, let $s\ge1$ be an integer, let $f:\mathbb F_2^n\to\{-1,+1\}$ be Boolean, let $H\le\mathbb F_2^n$ be any subspace, and fix a complement $W$ of the annihilator $H^\perp$, so $\mathbb F_2^n=W\oplus H^\perp$. For a shift $a$ and $\gamma\in W$ write $\hat f_{a+H}(\gamma)=\mathbb E_{h\in H}f(a+h)\chi_\gamma(h)$ for the restricted spectrum. Let $\rho=p_H(f)$ be the rejection probability of the checks of Algorithm 1 for this fixed $H$ over independent uniform shifts $a,r$, and assume $\rho<1/8$. Put $S_0=\operatorname{supp}(\hat f_H)$. The vote of a shift $r$ at $a$ is the vector $\hat\phi^r_{a+H}(\gamma)=\hat f_{a+r+H}(\gamma)\hat f_{r+H}(\gamma)/\hat f_H(\gamma)$ for $\gamma\in S_0$ and $0$ otherwise (Eq. (6)), and the corrected spectrum $\hat\phi_{a+H}$ is the most frequent entire vote vector among the $2^n$ votes, ties broken by a fixed rule.
--
--   **Claim 3.3.** For every $a\in\mathbb F_2^n$,
--   $$\Pr_r\big[\hat\phi^r_{a+H}=\hat\phi_{a+H}\big]\ge1-2\rho,$$
--   equality of entire vectors indexed by $W$. Moreover the corrected spectrum is a strict-majority vote (more than half of the $2^n$ shifts $r$ vote for it) and every other vector receives strictly fewer votes, so the tie-breaking rule is never invoked.
--
--   This pointwise guarantee, valid at every coset including bad ones, drives Claims 3.4, 3.6 and 3.7.
--
--   Differences from the source:
--
--   - encoding: the standing assumptions of §3.2 (s ≥ 1, H any subspace, W a fixed complement of H^⊥, ρ = p_H(f) < 1/8), stated once at the top of the section → explicit binders hs, hW, hρ of the theorem; reason: Lean statements carry every section assumption as a hypothesis; no other assumption is added
--   - encoding: ties in the most frequent vote are broken by a fixed rule → the fixed rule is Lean's choice function (winningShift); reason: any fixed rule is allowed by the source; the claims show ties never occur
--   - encoding: Boolean f : F₂ⁿ → {−1,+1} → bit function f : (Fin n → ZMod 2) → Bool with false ↦ +1, true ↦ −1 (toSign); reason: bijective encoding of Boolean functions; same instances
--   - encoding: the corrected spectrum is the unique strict-majority vote, and the tie-breaking rule is never invoked → 2ⁿ < 2·count(corrected) and every vector v ≠ corrected has count(v) < count(corrected); reason: literal rendering of strict majority and of the absence of ties
-- source:
--   Arijit Ghosh, Manmatha Roy, STOC 2027 submission #1656 (October 2026), p. 11, Claim 3.3 (standing setup p. 10, §3.2); PDF SHA256 5374116f8d05176f80f62c5fdaaddae029e1f9e6af853c5a8e1873cb4e83a123

import Mathlib
import Definitions.Def_FourierSparseTesting1656_Uniform_Correction

set_option autoImplicit false
open FourierDimTesting102.Quantum
open Classical

namespace FourierSparseTesting1656.Uniform

/-- Claim 3.3, p.11: for every shift `a`, the vote of a uniform `r` equals the corrected
spectrum with probability at least `1 - 2ρ`; the corrected spectrum is a strict-majority vote and
every other vector occurs strictly less often, so the tie-breaking rule is never invoked. -/
theorem claim_3_3 {n : ℕ} (s : ℕ) (hs : 1 ≤ s)
    (H W : Submodule (ZMod 2) (V n)) (hW : IsComplementOfPerp H W) (f : BoolFn n)
    (hρ : pH s H W f < 1 / 8) :
    ∀ a : V n,
      1 - 2 * pH s H W f ≤ (voteCount H W f a (corrected H W f a) : ℝ) / 2 ^ n ∧
      2 ^ n < 2 * voteCount H W f a (corrected H W f a) ∧
      ∀ v : W → ℝ, v ≠ corrected H W f a →
        voteCount H W f a v < voteCount H W f a (corrected H W f a) := by sorry

end FourierSparseTesting1656.Uniform
