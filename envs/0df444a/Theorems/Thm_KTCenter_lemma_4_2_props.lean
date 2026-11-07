-- Prove2me | Theorems.Thm_KTCenter_lemma_4_2_props
-- name    : KTCenter.lemma_4_2_props
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:28:23.559366+00:00
-- url     : https://prove2.me/theorems/3c781545-34fc-42d0-b264-ce6c2ce44d71
-- title:
--   Lemma 4.2, without its time clause — (3), $|E_J|\le 2rR^*$, $w_v\le5(d-1)$, $W\le20rR^*$, at most $(n+1)^r$ index sets
-- statement:
--   Relabel the candidates so that $\rho=\pi_1=(1,\dots,d)$, and let $r\ge1$ be an integer. For every $J\subseteq[n]$ with $1\in J$ and $|J|\le r$:
--
--   1. $E_J$ satisfies (3): if $a<v<b$ and $\{a,b\}\in E_J$, then $\{a,v\}\in E_J$ or $\{v,b\}\in E_J$;
--   2. $|E_J|\le 2rR^*$;
--   3. $0\le w_v\le 5(d-1)$ for every $v$;
--   4. $W=10|E_J|\le 20rR^*$.
--
--   Moreover, there are at most $(n+1)^r$ such index sets $J$.
--
--   This bounds the total movement allowance by a constant multiple of the optimum, which keeps all later additive errors small. The running-time clause of Lemma 4.2 is not part of this item; it is carried by the goal theorem.
--
--   Differences from the source:
--
--   - encoding: candidates relabeled by their position in the first input, so ρ = π₁ = (1, …, d) (§4.1) → hypothesis `I.π I.first = 1` on the input list; reason: the relabeling preserves all distances and is undone at the end (p.17); the statements of §§4–5 are about relabeled inputs
--   - encoding: 0 ≤ w_v → holds by the type ℕ; reason: Lean convention; same content
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), Lemma 4.2, p.17 (PDF p.19), with eq. (3), p.14 (PDF p.16)

import Mathlib
import Definitions.Def_KTCenter_Instance
import Definitions.Def_KTCenter_InversionUnion

namespace KTCenter

/-- **Lemma 4.2**, without its time clause, p.17 (PDF p.19), with eq. (3), p.14 (PDF p.16); the time
is carried by the goal.

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…).

**Formalization Note.** On relabeled inputs: `π₁ = 1` (§4.1). `0 ≤ w_v` holds by the type `ℕ`. The
last clause counts the index sets `J ⊆ [n]` with `1 ∈ J` and `|J| ≤ r`, as enumerated by Algorithm 1,
for an integer `r ≥ 1`. -/
theorem lemma_4_2_props (I : Instance) (hρ : I.π I.first = 1) (r : ℕ) (hr : 1 ≤ r) :
    (∀ J : Finset (Fin I.n), I.first ∈ J → J.card ≤ r →
      (∀ a v b : Fin I.d, a < v → v < b → (a, b) ∈ EJ I J → (a, v) ∈ EJ I J ∨ (v, b) ∈ EJ I J) ∧
      (EJ I J).card ≤ 2 * r * optRadius I ∧
      (∀ v, allowance I J v ≤ 5 * (I.d - 1)) ∧
      totalW (allowance I J) = 10 * (EJ I J).card ∧
      totalW (allowance I J) ≤ 20 * r * optRadius I) ∧
    (Finset.univ.filter fun J : Finset (Fin I.n) => I.first ∈ J ∧ J.card ≤ r).card ≤ (I.n + 1) ^ r := by sorry

end KTCenter
