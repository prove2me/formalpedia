-- Prove2me | Theorems.Thm_LinMaxLoad_lemma_7
-- name    : LinMaxLoad.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:35:47.487593+00:00
-- url     : https://prove2.me/theorems/b37e5488-5cf5-43a5-8a54-9d77d1ac42dd
-- title:
--   Lemma 7 (Quotient max load) — $\mathbb E_h[M(V+T,h)] \le 2\,\mathbb E_{h'}[M(T',h')]$
-- statement:
--   Let $K$ be a finite field, $E$ a finite $K$-vector space, $V \le E$ a subspace of dimension $d \le \ell$, and $T \subseteq E$ a finite set. Denote
--
--   $$
--   T' := \{t + V : t \in T\} \subseteq E/V .
--   $$
--
--   Let $h : E \to K^\ell$ and $h' : E/V \to K^{\ell - d}$ be uniformly random linear maps. Then
--
--   $$
--   \mathbb E_h\big[M(V + T, h)\big] \le 2\, \mathbb E_{h'}\big[M(T', h')\big].
--   $$
--
--   The lemma reduces hashing a union of cosets of $V$ to hashing the set of cosets in the quotient, losing only a factor $2$. In Theorem 17 it turns each piece $V_i + T_i$ into a small set $T_i'$ to which Theorem 7 applies.
--
--   Differences from the source:
--   - generalization: $\mathbb F_p^u$ and the field $\mathbb F_p$ → any finite $K$-module $E$ over any finite field $K$ ($q = |K|$); reason: the argument uses only linear algebra over a finite field; $K = \mathbb F_p$, $E = \mathbb F_p^u$ (`ZMod p`, `Fin u → ZMod p`) is the source statement
--   - encoding: $\ell - d$ → natural-number subtraction `ℓ - finrank V`; reason: exact because $d \le \ell$ is a hypothesis
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), Lemma 7 (Quotient max load), p.21

import Mathlib
import Definitions.Def_LinMaxLoad_cosetSum
import Definitions.Def_LinMaxLoad_expLoad

namespace LinMaxLoad

open Classical in
/-- **Lemma 7 (Quotient max load)** (p.21 of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)).
Let `V ≤ E` have dimension `d ≤ ℓ`, let `T ⊆ E` be finite and `T′ := {t + V : t ∈ T} ⊆ E/V`.
Let `h : E → K^ℓ` and `h′ : E/V → K^{ℓ−d}` be uniformly random linear maps. Then
`E_h[M(V + T, h)] ≤ 2 E_{h′}[M(T′, h′)]`.

**Formalization Note** `E = F_p^u`, `K = F_p` on the page; here `K` is any finite field and `E`
any finite `K`-module. `ℓ − d` is natural subtraction, exact since `d ≤ ℓ`. -/
theorem lemma_7 {K E : Type*} [Field K] [Fintype K] [AddCommGroup E] [Module K E] [Finite E]
    (ℓ : ℕ) (V : Submodule K E) (hV : Module.finrank K V ≤ ℓ) (T : Finset E) :
    expLoad K E ℓ (cosetSum V T) ≤
      2 * expLoad K (E ⧸ V) (ℓ - Module.finrank K V) (T.image V.mkQ) := by sorry

end LinMaxLoad
