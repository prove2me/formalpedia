-- Prove2me | Theorems.Thm_LinMaxLoad_lemma_7_conditional_bound
-- name    : LinMaxLoad.lemma_7_conditional_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:36:01.320967+00:00
-- url     : https://prove2.me/theorems/2fed27ce-133f-411d-be9f-f20a9465e8e1
-- title:
--   Proof of Lemma 7 — conditional bound $\mathbb E_h[M(V+T,h)\mid h|_V] \le q^r\,\mathbb E_{h'}[M(T',h')]$
-- statement:
--   Let $K$ be a finite field with $q$ elements, $E$ a finite $K$-vector space, $V \le E$ a subspace of dimension $d \le \ell$, $T \subseteq E$ finite, and $T' := \{t + V : t \in T\} \subseteq E/V$. Let $h : E \to K^\ell$ and $h' : E/V \to K^{\ell - d}$ be uniformly random linear maps. For every linear map $\varphi : V \to K^\ell$, conditioning on the event $h|_V = \varphi$,
--
--   $$
--   \mathbb E_h\big[M(V + T, h) \,\big|\, h|_V = \varphi\big] \le q^{r}\, \mathbb E_{h'}\big[M(T', h')\big], \qquad r = \dim \ker \varphi .
--   $$
--
--   On this event $r = \dim\ker(h|_V)$, so this is the page's bound $\mathbb E_h[M(V+T,h) \mid h|_V] \le q^r\, \mathbb E_{h'}[M(T',h')]$. It is the step of Lemma 7 that compares hashing a union of cosets with hashing the cosets in the quotient.
--
--   Differences from the source:
--   - generalization: $\mathbb F_p^u$ and the field $\mathbb F_p$ → any finite $K$-module $E$ over any finite field $K$ ($q = |K|$); reason: the argument uses only linear algebra over a finite field; $K = \mathbb F_p$, $E = \mathbb F_p^u$ (`ZMod p`, `Fin u → ZMod p`) is the source statement
--   - encoding: $\mathbb E_h[\,\cdot \mid h|_V]$, a random variable → for every value $\varphi$ of $h|_V$, the average over the maps $h$ with $h \circ (V \hookrightarrow E) = \varphi$ (`condAvgLin`); reason: conditioning on a discrete random variable; every value $\varphi$ is attained
--   - encoding: $\ell - d$ → natural-number subtraction `ℓ - finrank V`; reason: exact because $d \le \ell$ is a hypothesis
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), proof of Lemma 7, conditional bound, p.21

import Mathlib
import Definitions.Def_LinMaxLoad_maxLoad
import Definitions.Def_LinMaxLoad_cosetSum
import Definitions.Def_LinMaxLoad_expLoad
import Definitions.Def_LinMaxLoad_condAvgLin

namespace LinMaxLoad

open Classical in
/-- **Proof of Lemma 7, conditional bound** (p.21 of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)).
Let `V ≤ E` have dimension `d ≤ ℓ`, `T ⊆ E` finite, `T′ := {t + V : t ∈ T} ⊆ E/V`, `h : E → K^ℓ`
and `h′ : E/V → K^{ℓ−d}` uniformly random linear maps. Conditioned on `h|_V = φ`,
`E_h[M(V + T, h) | h|_V = φ] ≤ q^r · E_{h′}[M(T′, h′)]` with `r = dim ker φ` (`= dim ker(h|_V)`)
and `q = |K|`.

**Formalization Note** The conditional expectation given `h|_V` is written for every possible
value `φ : V → K^ℓ` of the restriction, as the uniform average (`condAvgLin`) over the linear
maps `h` with `h ∘ (V ↪ E) = φ` (a nonempty set: every `φ` extends). `E = F_p^u`, `K = F_p` on
the page; here `K` is any finite field and `E` any finite `K`-module. -/
theorem lemma_7_conditional_bound {K E : Type*} [Field K] [Fintype K] [AddCommGroup E]
    [Module K E] [Finite E] (ℓ : ℕ) (V : Submodule K E) (hV : Module.finrank K V ≤ ℓ)
    (T : Finset E) (φ : V →ₗ[K] (Fin ℓ → K)) :
    condAvgLin K E ℓ (fun h => h.comp V.subtype = φ)
        (fun h => (maxLoad (h : E → Fin ℓ → K) (cosetSum V T) : ℝ)) ≤
      (Fintype.card K : ℝ) ^ Module.finrank K (LinearMap.ker φ) *
        expLoad K (E ⧸ V) (ℓ - Module.finrank K V) (T.image V.mkQ) := by sorry

end LinMaxLoad
