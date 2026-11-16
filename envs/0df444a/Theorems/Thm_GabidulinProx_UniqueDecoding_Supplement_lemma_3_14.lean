-- Prove2me | Theorems.Thm_GabidulinProx_UniqueDecoding_Supplement_lemma_3_14
-- name    : GabidulinProx.UniqueDecoding.Supplement.lemma_3_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:44:47.821958+00:00
-- url     : https://prove2.me/theorems/313a5bc0-5737-4c2f-914d-627c25e12c88
-- title:
--   Lemma 3.14 — the parameter set $H$ has exactly $(q^n-1)/(q-1)$ elements
-- statement:
--   Fix integers $r\ge1$ and $2\le c\le h$, put $n=c(r+1)$, $m=h(r+1)$ and $Q=q^{r+1}$. Let $\mathbb F_q\subseteq\mathbb F_Q\subseteq E=\mathbb F_{q^m}=\mathbb F_{Q^h}$ and let $V\subseteq E$ be any $c$-dimensional $\mathbb F_Q$-subspace. For an $\mathbb F_Q$-subspace $W\subseteq V$ let $A_W(X)=\prod_{w\in W}(X-w)$. Define
--
--   $$H=\bigl\{-A_W(x)^{q-1}:\ W\subseteq V\text{ an }\mathbb F_Q\text{-subspace},\ \dim_{\mathbb F_Q}W=c-1,\ x\in V\setminus W\bigr\}\subseteq E .$$
--
--   Then, counting distinct field elements,
--
--   $$|H|=\frac{q^n-1}{q-1}.$$
--
--   The count gives the probability lower bound of Theorems 1.5 and 3.15.
--
--   Differences from the source:
--   - encoding: finite fields $\mathbb F_q\subseteq\mathbb F_{q^m}$ → finite fields $K,L$ with an algebra structure, $q=|K|$, $q^m=|L|$; reason: every finite extension of $\mathbb F_q$ has this form, and $|L|=|K|^{[L:K]}$
--   - encoding: the subfield $\mathbb F_Q$, $Q=q^{r+1}$, of $E=\mathbb F_{Q^h}$ → an intermediate finite field `KQ` with `IsScalarTower K KQ E`, $|KQ|=q^{r+1}$ and $[E:KQ]=h$; reason: a finite field has exactly one subfield of each admissible size; $m=h(r+1)$ follows
--   - encoding: $\dim W=c-1$ and the exact cardinality $(q^n-1)/(q-1)$ → $\dim W=\dim V-1$ inside the published-style set `paramSet`, and `ncard` equal to $(q^n-1)/(q-1)$ computed in $\mathbb R$; reason: $\dim V=c$ is a hypothesis; $q\ge2$ so the real quotient is the exact integer count
-- source:
--   Songsong Li, Chaoping Xing, Chen Yuan, Ruiqi Zhu, Proximity Gaps for Gabidulin Codes and Applications, STOC 2027 submission #434 (October 2026), §3.4 setting and Lemma 3.14 p.28. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/434.pdf, SHA-256 8f644bcdfbdcd3478384d77d75a0f88ea116c29b14c52714f58bffb9ffda25cf

import Definitions.Def_GabidulinProx_UniqueDecoding_Supplement_Objects

namespace GabidulinProx.UniqueDecoding.Supplement

open GabidulinProx.UniqueDecoding

/-- Lemma 3.14, p.28: let `K ⊆ KQ ⊆ E` be finite fields, `q = |K|`, `|KQ| = Q = q^(r+1)`,
`[E : KQ] = h`, `r ≥ 1`, `2 ≤ c ≤ h`, `n = c(r+1)`, and `V` a `c`-dimensional `KQ`-subspace of
`E`. The set `H = {-A_W(x)^(q-1) : W ⊆ V, dim W = c-1, x ∈ V \ W}` has exactly
`(q^n - 1)/(q - 1)` elements. -/
theorem lemma_3_14 {K KQ E : Type*} [Field K] [Fintype K] [Field KQ] [Fintype KQ]
    [Field E] [Fintype E] [Algebra K KQ] [Algebra KQ E] [Algebra K E] [IsScalarTower K KQ E]
    (r c h : ℕ) (hr : 1 ≤ r) (hc : 2 ≤ c) (hch : c ≤ h)
    (hQ : Fintype.card KQ = Fintype.card K ^ (r + 1)) (hE : Module.finrank KQ E = h)
    (V : Submodule KQ E) (hV : Module.finrank KQ V = c) :
    ((paramSet K KQ V).ncard : ℝ) =
      ((Fintype.card K : ℝ) ^ (c * (r + 1)) - 1) / ((Fintype.card K : ℝ) - 1) := by sorry
end GabidulinProx.UniqueDecoding.Supplement
