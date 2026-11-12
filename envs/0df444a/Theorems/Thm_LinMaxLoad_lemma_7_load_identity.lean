-- Prove2me | Theorems.Thm_LinMaxLoad_lemma_7_load_identity
-- name    : LinMaxLoad.lemma_7_load_identity
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T16:34:46.324247+00:00
-- url     : https://prove2.me/theorems/0021e7b8-bc4a-4fc5-84f1-cd75a141385b
-- title:
--   Proof of Lemma 7 — load identity $M(V+T,h) = q^r M(T',g_h)$
-- statement:
--   Let $K$ be a finite field with $q$ elements, $E$ a finite $K$-vector space, $V \le E$ a subspace, $T \subseteq E$ a finite set, and $h : E \to K^\ell$ a linear map. Put
--
--   1. $H := h(V) \le K^\ell$ and $r := \dim \ker(h|_V)$;
--   2. $T' := \{t + V : t \in T\} \subseteq E/V$;
--   3. $g_h : E/V \to K^\ell/H$, $x + V \mapsto h(x) + H$, the induced linear map.
--
--   Then
--
--   $$
--   M(V + T, h) = q^{r}\, M(T', g_h).
--   $$
--
--   Each coset $V + t$ that $g_h$ sends to the class of $y$ meets $h^{-1}(y)$ in a translate of $\ker(h|_V)$, so the identity converts the max load of a union of cosets into the max load of the cosets themselves under the induced map. It is the first step of Lemma 7.
--
--   Differences from the source:
--   - generalization: $\mathbb F_p^u$ and the field $\mathbb F_p$ → any finite $K$-module $E$ over any finite field $K$ ($q = |K|$); reason: the argument uses only linear algebra over a finite field; $K = \mathbb F_p$, $E = \mathbb F_p^u$ (`ZMod p`, `Fin u → ZMod p`) is the source statement
--   - generalization: $T$ whose elements lie in distinct cosets of $V$ (assumed without loss of generality on the page) → any finite $T$, with $T' = \{t + V : t \in T\}$ its image in $E/V$; reason: duplicates change neither $V + T$ nor $T'$, so the identity for all $T$ specializes to the page's case
--   - encoding: $g_h$, $x + V \mapsto h(x) + H$ → `Submodule.mapQ V (V.map h) h _`; reason: the same induced map
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), proof of Lemma 7, load identity, p.21

import Mathlib
import Definitions.Def_LinMaxLoad_maxLoad
import Definitions.Def_LinMaxLoad_cosetSum

namespace LinMaxLoad

open Classical in
/-- **Proof of Lemma 7, load identity** (p.21 of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)).
Let `V ≤ E`, `T ⊆ E` finite and `h : E → K^ℓ` linear. Put `H := h(V)`,
`r := dim ker(h|_V)`, `T′ := {t + V : t ∈ T} ⊆ E/V`, and let `g_h : E/V → K^ℓ/H`,
`x + V ↦ h(x) + H`, be the induced linear map. Then `M(V + T, h) = q^r · M(T′, g_h)`,
`q = |K|`.

**Formalization Note** `E = F_p^u`, `K = F_p` on the page; here `K` is any finite field and `E`
any finite `K`-module. `g_h` is `Submodule.mapQ V (V.map h) h _`, `T′` is the image of `T` under
the quotient map (duplicate cosets in `T` are allowed: the page removes them without loss).
Decidable equality is classical. -/
theorem lemma_7_load_identity {K E : Type*} [Field K] [Fintype K] [AddCommGroup E]
    [Module K E] [Finite E] (ℓ : ℕ) (V : Submodule K E) (T : Finset E)
    (h : E →ₗ[K] (Fin ℓ → K)) :
    maxLoad (h : E → Fin ℓ → K) (cosetSum V T) =
      Fintype.card K ^ Module.finrank K (LinearMap.ker (h.domRestrict V)) *
        maxLoad (Submodule.mapQ V (V.map h) h (Submodule.le_comap_map h V) :
          E ⧸ V → (Fin ℓ → K) ⧸ V.map h) (T.image V.mkQ) := by sorry

end LinMaxLoad
