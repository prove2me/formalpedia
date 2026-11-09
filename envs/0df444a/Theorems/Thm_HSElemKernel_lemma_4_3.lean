-- Prove2me | Theorems.Thm_HSElemKernel_lemma_4_3
-- name    : HSElemKernel.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:24:51.502118+00:00
-- url     : https://prove2.me/theorems/41d29d13-a9cf-4f0d-b331-f906d2a5fc18
-- title:
--   Lemma 4.3 — each subbucket represents at most one element; $|\{v : D_{\sigma,v}\}| \le \sum a_{c,j}$
-- statement:
--   Let $\mathcal F$ be a two-level hash pair on $W$, $\gamma : W \to \{0,1\}^\ell$ an address map giving distinct addresses to the elements of $W$, $\sigma : [B] \to [t]$, and fix an assignment $a_{c,j}$, $z_{c,j,\beta}$ of the table variables. Then the variables of each subbucket represent at most one element of $W$: if $u, v \in W$ lie in the same subbucket $H_\sigma(u) = H_\sigma(v)$ and both $D_{\sigma,u}$ and $D_{\sigma,v}$ hold, then $u = v$. Consequently,
--   $$\big|\{v \in W : D_{\sigma,v} = 1\}\big| \le \sum_{c=1}^{B} \sum_{j=1}^{q_2} a_{c,j}.$$
--
--   The lemma bounds the number of elements of $W$ the table represents by the number of active subbuckets, which is what constraint (6) counts.
--
--   Differences from the source:
--   - generalization: W = U \ X and the address map γ : W → {0,1}^ℓ with ℓ = ⌈log₂(|W|+1)⌉ → any finite W in any type, any ℓ and any γ injective on W; reason: the proof uses only that addresses are distinct; it specializes to the paper's W, ℓ and γ
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Lemma 4.3, p.11

import Mathlib
import Definitions.Def_HSElemKernel_represented

namespace HSElemKernel

open Classical in
/-- **Lemma 4.3** (Sheng–Xiao, *A Near-Linear Element-Kernel for d-Hitting Set*, arXiv:2609.06512 (held version, sha256 aca9c70e…), Lemma 4.3, p.11): fix `σ` and an assignment `a, z` to the table
variables. The variables of each subbucket represent at most one element of `W`; consequently
$$|\{v ∈ W : D_{σ,v} = 1\}| ≤ \sum_{c=1}^{B} \sum_{j=1}^{q₂} a_{c,j}.$$

Here `γ` gives distinct addresses to the elements of `W` (Section 4.2, p.10) and `D_{σ,v}` is
`represented` (Eq. (4)).

**Formalization Note** `W` is a finite subset of an arbitrary type `α` on which `F` is
defined; addresses have any length `ℓ`. -/
theorem lemma_4_3 {α : Type} (F : TwoLevelHash α) {ℓ : ℕ} (γ : α → Fin ℓ → Bool)
    (W : Finset α) (hγ : Set.InjOn γ (W : Set α)) (σ : Fin F.B → Fin F.t)
    (a : Fin F.B → Fin F.q2 → Bool) (z : Fin F.B → Fin F.q2 → Fin ℓ → Bool) :
    (∀ (c : Fin F.B) (j : Fin F.q2), ∀ u ∈ W, ∀ v ∈ W,
        (F.h u, F.g (σ (F.h u)) u) = (c, j) → (F.h v, F.g (σ (F.h v)) v) = (c, j) →
        represented F γ σ a z u → represented F γ σ a z v → u = v) ∧
      (W.filter (represented F γ σ a z)).card ≤ ∑ c, ∑ j, (a c j).toNat := by sorry

end HSElemKernel
