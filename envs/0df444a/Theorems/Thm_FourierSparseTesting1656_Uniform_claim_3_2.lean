-- Prove2me | Theorems.Thm_FourierSparseTesting1656_Uniform_claim_3_2
-- name    : FourierSparseTesting1656.Uniform.claim_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:33:41.579337+00:00
-- url     : https://prove2.me/theorems/c616812d-02d8-4495-822f-42eac3fd588a
-- title:
--   Claim 3.2 — corrected spectra agree with $f$ on most cosets
-- statement:
--   **Standing setup (§3.2, p.10).** Let $n\ge0$, let $s\ge1$ be an integer, let $f:\mathbb F_2^n\to\{-1,+1\}$ be Boolean, let $H\le\mathbb F_2^n$ be any subspace, and fix a complement $W$ of the annihilator $H^\perp$, so $\mathbb F_2^n=W\oplus H^\perp$. For a shift $a$ and $\gamma\in W$ write $\hat f_{a+H}(\gamma)=\mathbb E_{h\in H}f(a+h)\chi_\gamma(h)$ for the restricted spectrum. Let $\rho=p_H(f)$ be the rejection probability of the checks of Algorithm 1 for this fixed $H$ over independent uniform shifts $a,r$, and assume $\rho<1/8$. Put $S_0=\operatorname{supp}(\hat f_H)$. The vote of a shift $r$ at $a$ is the vector $\hat\phi^r_{a+H}(\gamma)=\hat f_{a+r+H}(\gamma)\hat f_{r+H}(\gamma)/\hat f_H(\gamma)$ for $\gamma\in S_0$ and $0$ otherwise (Eq. (6)), and the corrected spectrum $\hat\phi_{a+H}$ is the most frequent entire vote vector among the $2^n$ votes, ties broken by a fixed rule.
--
--   **Claim 3.2.** For all but a $2\rho$ fraction of the shifts $a$, the corrected spectrum equals the true restricted spectrum,
--   $$\frac{|\{a\in\mathbb F_2^n:\hat\phi_{a+H}\ne\hat f_{a+H}\}|}{2^n}\le2\rho,$$
--   and every real-valued function $\phi:\mathbb F_2^n\to\mathbb R$ whose restriction spectrum on every coset $a+H$ equals $\hat\phi_{a+H}$ satisfies $\operatorname{dist}(f,\phi)\le2\rho$.
--
--   This is the step that ties the corrected function back to $f$; it is used for the distance bound in Proposition 3.8.
--
--   Differences from the source:
--
--   - encoding: the standing assumptions of §3.2 (s ≥ 1, H any subspace, W a fixed complement of H^⊥, ρ = p_H(f) < 1/8), stated once at the top of the section → explicit binders hs, hW, hρ of the theorem; reason: Lean statements carry every section assumption as a hypothesis; no other assumption is added
--   - encoding: ties in the most frequent vote are broken by a fixed rule → the fixed rule is Lean's choice function (winningShift); reason: any fixed rule is allowed by the source; the claims show ties never occur
--   - encoding: Boolean f : F₂ⁿ → {−1,+1} → bit function f : (Fin n → ZMod 2) → Bool with false ↦ +1, true ↦ −1 (toSign); reason: bijective encoding of Boolean functions; same instances
--   - encoding: all but a 2ρ fraction of the cosets a + H → the fraction of shifts a ∈ F₂ⁿ with corrected ≠ actual spectrum is at most 2ρ; reason: all cosets have the same size and, by Eqs. (7) and (11), the event does not depend on the representative, so the two fractions coincide
--   - encoding: once these corrected spectra are realized by a global function ϕ → for every real φ whose restriction spectra equal the corrected spectra on every coset; reason: the source's conditional clause, with no Booleanity of φ assumed
-- source:
--   Arijit Ghosh, Manmatha Roy, STOC 2027 submission #1656 (October 2026), p. 10, Claim 3.2 (standing setup p. 10, §3.2); PDF SHA256 5374116f8d05176f80f62c5fdaaddae029e1f9e6af853c5a8e1873cb4e83a123

import Mathlib
import Definitions.Def_FourierSparseTesting1656_Uniform_Correction

set_option autoImplicit false
open FourierDimTesting102.Quantum
open Classical

namespace FourierSparseTesting1656.Uniform

/-- Claim 3.2, p.10: under the standing setup of §3.2 (`ρ = p_H(f) < 1/8`), the corrected
spectrum equals the actual restriction spectrum for all but a `2ρ` fraction of shifts, and every
real function realizing all corrected spectra is within distance `2ρ` of `f`. -/
theorem claim_3_2 {n : ℕ} (s : ℕ) (hs : 1 ≤ s)
    (H W : Submodule (ZMod 2) (V n)) (hW : IsComplementOfPerp H W) (f : BoolFn n)
    (hρ : pH s H W f < 1 / 8) :
    ((Finset.univ.filter fun a : V n => corrected H W f a ≠ rspec H W f a).card : ℝ) / 2 ^ n
        ≤ 2 * pH s H W f ∧
    ∀ φ : V n → ℝ, (∀ (a : V n) (γ : W), restrCoeff H W φ a γ = corrected H W f a γ) →
      realDist (toSign f) φ ≤ 2 * pH s H W f := by sorry

end FourierSparseTesting1656.Uniform
