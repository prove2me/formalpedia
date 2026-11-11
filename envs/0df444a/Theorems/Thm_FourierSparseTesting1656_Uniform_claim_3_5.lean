-- Prove2me | Theorems.Thm_FourierSparseTesting1656_Uniform_claim_3_5
-- name    : FourierSparseTesting1656.Uniform.claim_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:33:24.208796+00:00
-- url     : https://prove2.me/theorems/307d08e2-bc41-4353-b023-52345df26ec8
-- title:
--   Claim 3.5 — a global real $s$-sparse function realizing every corrected spectrum
-- statement:
--   **Standing setup (§3.2, p.10).** Let $n\ge0$, let $s\ge1$ be an integer, let $f:\mathbb F_2^n\to\{-1,+1\}$ be Boolean, let $H\le\mathbb F_2^n$ be any subspace, and fix a complement $W$ of the annihilator $H^\perp$, so $\mathbb F_2^n=W\oplus H^\perp$. For a shift $a$ and $\gamma\in W$ write $\hat f_{a+H}(\gamma)=\mathbb E_{h\in H}f(a+h)\chi_\gamma(h)$ for the restricted spectrum. Let $\rho=p_H(f)$ be the rejection probability of the checks of Algorithm 1 for this fixed $H$ over independent uniform shifts $a,r$, and assume $\rho<1/8$. Put $S_0=\operatorname{supp}(\hat f_H)$. The vote of a shift $r$ at $a$ is the vector $\hat\phi^r_{a+H}(\gamma)=\hat f_{a+r+H}(\gamma)\hat f_{r+H}(\gamma)/\hat f_H(\gamma)$ for $\gamma\in S_0$ and $0$ otherwise (Eq. (6)), and the corrected spectrum $\hat\phi_{a+H}$ is the most frequent entire vote vector among the $2^n$ votes, ties broken by a fixed rule.
--
--   **Claim 3.5.** There is a real-valued $\phi:\mathbb F_2^n\to\mathbb R$ with Fourier sparsity $\operatorname{fs}(\phi)\le s$ such that for every $a$ the restriction spectrum of $\phi$ on $a+H$ equals the corrected spectrum,
--   $$\hat\phi_{a+H}(\gamma)=\mathbb E_{h\in H}\,\phi(a+h)\chi_\gamma(h)\quad(\gamma\in W),$$
--   and $\operatorname{supp}(\hat\phi_{a+H})\subseteq S_0$ for every $a$.
--
--   The function is real valued at this stage; that it is Boolean is Claim 3.7. One function serves all cosets.
--
--   Differences from the source:
--
--   - encoding: the standing assumptions of §3.2 (s ≥ 1, H any subspace, W a fixed complement of H^⊥, ρ = p_H(f) < 1/8), stated once at the top of the section → explicit binders hs, hW, hρ of the theorem; reason: Lean statements carry every section assumption as a hypothesis; no other assumption is added
--   - encoding: ties in the most frequent vote are broken by a fixed rule → the fixed rule is Lean's choice function (winningShift); reason: any fixed rule is allowed by the source; the claims show ties never occur
--   - encoding: Boolean f : F₂ⁿ → {−1,+1} → bit function f : (Fin n → ZMod 2) → Bool with false ↦ +1, true ↦ −1 (toSign); reason: bijective encoding of Boolean functions; same instances
--   - encoding: supp(ϕ̂_{a+H}) ⊆ S₀ → every γ with a nonzero restriction coefficient of φ on a + H lies in S₀ = supp(f̂_H); reason: the restriction coefficients of φ equal the corrected spectrum by the first clause, so this is the same support
-- source:
--   Arijit Ghosh, Manmatha Roy, STOC 2027 submission #1656 (October 2026), p. 13, Claim 3.5 (standing setup p. 10, §3.2); PDF SHA256 5374116f8d05176f80f62c5fdaaddae029e1f9e6af853c5a8e1873cb4e83a123

import Mathlib
import Definitions.Def_FourierSparseTesting1656_Uniform_Correction

set_option autoImplicit false
open FourierDimTesting102.Quantum
open Classical

namespace FourierSparseTesting1656.Uniform

/-- Claim 3.5, p.13: one real-valued `ϕ` on `F₂ⁿ` with Fourier sparsity at most `s` has, on
every coset `a + H`, restriction spectrum exactly the corrected spectrum, and that spectrum is
supported in `S₀ = supp(f̂_H)`. -/
theorem claim_3_5 {n : ℕ} (s : ℕ) (hs : 1 ≤ s)
    (H W : Submodule (ZMod 2) (V n)) (hW : IsComplementOfPerp H W) (f : BoolFn n)
    (hρ : pH s H W f < 1 / 8) :
    ∃ φ : V n → ℝ, realSparsity φ ≤ s ∧
      ∀ a : V n, (∀ γ : W, restrCoeff H W φ a γ = corrected H W f a γ) ∧
        ∀ γ : W, restrCoeff H W φ a γ ≠ 0 → rspec H W f 0 γ ≠ 0 := by sorry

end FourierSparseTesting1656.Uniform
