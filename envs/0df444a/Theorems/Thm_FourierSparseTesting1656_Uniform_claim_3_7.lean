-- Prove2me | Theorems.Thm_FourierSparseTesting1656_Uniform_claim_3_7
-- name    : FourierSparseTesting1656.Uniform.claim_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:33:39.698495+00:00
-- url     : https://prove2.me/theorems/9324e176-4e9e-491d-bc67-30b79f128e9a
-- title:
--   Claim 3.7 — corrected spectra satisfy the Boolean convolution identities
-- statement:
--   **Standing setup (§3.2, p.10).** Let $n\ge0$, let $s\ge1$ be an integer, let $f:\mathbb F_2^n\to\{-1,+1\}$ be Boolean, let $H\le\mathbb F_2^n$ be any subspace, and fix a complement $W$ of the annihilator $H^\perp$, so $\mathbb F_2^n=W\oplus H^\perp$. For a shift $a$ and $\gamma\in W$ write $\hat f_{a+H}(\gamma)=\mathbb E_{h\in H}f(a+h)\chi_\gamma(h)$ for the restricted spectrum. Let $\rho=p_H(f)$ be the rejection probability of the checks of Algorithm 1 for this fixed $H$ over independent uniform shifts $a,r$, and assume $\rho<1/8$. Put $S_0=\operatorname{supp}(\hat f_H)$. The vote of a shift $r$ at $a$ is the vector $\hat\phi^r_{a+H}(\gamma)=\hat f_{a+r+H}(\gamma)\hat f_{r+H}(\gamma)/\hat f_H(\gamma)$ for $\gamma\in S_0$ and $0$ otherwise (Eq. (6)), and the corrected spectrum $\hat\phi_{a+H}$ is the most frequent entire vote vector among the $2^n$ votes, ties broken by a fixed rule.
--
--   **Claim 3.7.** For every coset $a+H$ and every $\beta\in W$,
--   $$\sum_{\substack{\gamma,\gamma'\in W\\ \gamma+\gamma'=\beta}}\hat\phi_{a+H}(\gamma)\,\hat\phi_{a+H}(\gamma')=\begin{cases}1,&\beta=0,\\0,&\beta\ne0.\end{cases}\tag{16}$$
--   Consequently the function $\phi$ of Eq. (13), the real function whose restriction spectrum on every coset $a+H$ is $\hat\phi_{a+H}$, exists and is Boolean: $\phi(x)\in\{-1,+1\}$ for every $x$.
--
--   The $\beta=0$ identity is the unit-norm normalization and the $\beta\ne0$ identities are the Titsworth relations; together with Claim 3.5 they place $\phi$ in $F_s$.
--
--   Differences from the source:
--
--   - encoding: the standing assumptions of §3.2 (s ≥ 1, H any subspace, W a fixed complement of H^⊥, ρ = p_H(f) < 1/8), stated once at the top of the section → explicit binders hs, hW, hρ of the theorem; reason: Lean statements carry every section assumption as a hypothesis; no other assumption is added
--   - encoding: ties in the most frequent vote are broken by a fixed rule → the fixed rule is Lean's choice function (winningShift); reason: any fixed rule is allowed by the source; the claims show ties never occur
--   - encoding: Boolean f : F₂ⁿ → {−1,+1} → bit function f : (Fin n → ZMod 2) → Bool with false ↦ +1, true ↦ −1 (toSign); reason: bijective encoding of Boolean functions; same instances
--   - encoding: the function ϕ of Eq. (13) is Boolean → a real φ realizing every corrected spectrum exists, and every such φ is ±1-valued; reason: the restriction spectra on all cosets determine a function (the χ_γ|_H, γ ∈ W, form a basis), so the only realizer is the ϕ of Eq. (13)
-- source:
--   Arijit Ghosh, Manmatha Roy, STOC 2027 submission #1656 (October 2026), p. 14, Claim 3.7, Eq. (16) (standing setup p. 10, §3.2; ϕ of Eq. (13), p. 13); PDF SHA256 5374116f8d05176f80f62c5fdaaddae029e1f9e6af853c5a8e1873cb4e83a123

import Mathlib
import Definitions.Def_FourierSparseTesting1656_Uniform_Correction

set_option autoImplicit false
open FourierDimTesting102.Quantum
open Classical

namespace FourierSparseTesting1656.Uniform

/-- Claim 3.7, Eq. (16), p.14: every corrected spectrum satisfies the Boolean convolution
identities (`1` at `β = 0`, `0` at `β ≠ 0`, `β ∈ W`); consequently the real function realizing
all corrected spectra (the `ϕ` of Eq. (13)) exists and is `±1`-valued. -/
theorem claim_3_7 {n : ℕ} (s : ℕ) (hs : 1 ≤ s)
    (H W : Submodule (ZMod 2) (V n)) (hW : IsComplementOfPerp H W) (f : BoolFn n)
    (hρ : pH s H W f < 1 / 8) :
    (∀ (a : V n) (β : W),
      ∑ p ∈ Finset.univ.filter (fun p : W × W => p.1 + p.2 = β),
          corrected H W f a p.1 * corrected H W f a p.2 = if β = 0 then 1 else 0) ∧
    (∃ φ : V n → ℝ, ∀ (a : V n) (γ : W), restrCoeff H W φ a γ = corrected H W f a γ) ∧
    ∀ φ : V n → ℝ, (∀ (a : V n) (γ : W), restrCoeff H W φ a γ = corrected H W f a γ) →
      ∀ x : V n, φ x = 1 ∨ φ x = -1 := by sorry

end FourierSparseTesting1656.Uniform
