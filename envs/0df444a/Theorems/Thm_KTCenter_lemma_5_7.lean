-- Prove2me | Theorems.Thm_KTCenter_lemma_5_7
-- name    : KTCenter.lemma_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:31:15.75574+00:00
-- url     : https://prove2.me/theorems/402b66f3-198a-4956-949a-f3b3e8f418de
-- title:
--   Lemma 5.7 — cost values, single-key change bounds $\lambda_v$, and $\sum_v\lambda_v=C_1W$
-- statement:
--   Let $(w_v)$ be nonnegative integers, $0<\beta<1$, $0<\zeta<1$, and $\pi_i$ a ranking. For the output of Algorithm 3:
--
--   1. $A_i\ge0$ and $u_{iv}(a)\ge0$ for $v\in U$, $a\in P_v$;
--   2. for distinct $u,v\in U$ and keys $a\in P_u$, $b\in P_v$: $q_i(u,a,v,b)\in\{0,1\}$ and $q_i(v,b,u,a)=q_i(u,a,v,b)$;
--   3. $q_i(u,a,v,b)=0$ when $u,v$ lie in different sets of $\mathcal B$, and $q_i(v,a,v,b)=0$;
--   4. for $v\in U$ and allowed $p,p'$ agreeing outside $v$: $|\tilde C_i(p)-\tilde C_i(p')|\le\lambda_v$;
--   5. $\sum_{v\in U}\lambda_v=C_1W$.
--
--   Together with Lemmas 5.2 and 5.6 this shows that Algorithm 3 produces a cost instance satisfying (7).
--
--   Differences from the source:
--
--   - generalization: allowances of the fixed tuple and an input π_i → arbitrary nonnegative integer allowances and an arbitrary ranking; reason: the construction and proof use nothing else; it specializes to the source
--   - encoding: p, p′ ∈ 𝒫(U) agreeing on U \ {v} → full key vectors agreeing at every u ≠ v; reason: outside U the keys are fixed, so the conditions coincide
--   - encoding: A_i ≥ 0, u_iv ≥ 0 → hold by the type ℕ, kept as conjuncts; reason: Lean convention
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), Lemma 5.7, p.35 (PDF p.37)

import Mathlib
import Definitions.Def_KTCenter_KeyDomains
import Definitions.Def_KTCenter_PartitionCosts

namespace KTCenter

/-- **Lemma 5.7** (Cost values and the effect of changing one key), p.35 (PDF p.37).

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…).

**Formalization Note.** Algorithms 2 and 3 for any allowances `w` and any ranking `ρ = πᵢ`. The clause
on `Aᵢ` and `uᵢᵥ` holds by the type `ℕ`, and is kept as written. `p`, `p′` are full key vectors, which
agree outside `v` on `U` and also outside `U`. -/
theorem lemma_5_7 {d : ℕ} (w : Fin d → ℕ) (β ζ : ℚ) (hβ0 : 0 < β) (hβ1 : β < 1) (hζ0 : 0 < ζ)
    (hζ1 : ζ < 1) (ρ : Equiv.Perm (Fin d)) :
    0 ≤ PartitionCosts.constA w β ρ ∧
    (∀ v ∈ PartitionCosts.varSet w, ∀ a ∈ keySet w β v, 0 ≤ PartitionCosts.singleKey w β ζ ρ v a) ∧
    (∀ u ∈ PartitionCosts.varSet w, ∀ v ∈ PartitionCosts.varSet w, u ≠ v →
      ∀ a ∈ keySet w β u, ∀ b ∈ keySet w β v,
        (PartitionCosts.pairQ w β ζ ρ u a v b = 0 ∨ PartitionCosts.pairQ w β ζ ρ u a v b = 1) ∧
        PartitionCosts.pairQ w β ζ ρ v b u a = PartitionCosts.pairQ w β ζ ρ u a v b) ∧
    (∀ B ∈ PartitionCosts.blocks w β ζ, ∀ B' ∈ PartitionCosts.blocks w β ζ, B ≠ B' →
      ∀ u ∈ B, ∀ v ∈ B', ∀ a ∈ keySet w β u, ∀ b ∈ keySet w β v,
        PartitionCosts.pairQ w β ζ ρ u a v b = 0) ∧
    (∀ v ∈ PartitionCosts.varSet w, ∀ a ∈ keySet w β v, ∀ b ∈ keySet w β v,
      PartitionCosts.pairQ w β ζ ρ v a v b = 0) ∧
    (∀ v ∈ PartitionCosts.varSet w, ∀ p ∈ assignments w β, ∀ p' ∈ assignments w β,
      (∀ u, u ≠ v → p u = p' u) →
      |(PartitionCosts.surrogate w β ζ ρ p : ℚ) - (PartitionCosts.surrogate w β ζ ρ p' : ℚ)| ≤
        PartitionCosts.lam w ζ v) ∧
    ∑ v ∈ PartitionCosts.varSet w, PartitionCosts.lam w ζ v =
      PartitionCosts.constC1 ζ * (totalW w : ℚ) := by sorry

end KTCenter
