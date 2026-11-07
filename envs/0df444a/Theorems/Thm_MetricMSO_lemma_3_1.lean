-- Prove2me | Theorems.Thm_MetricMSO_lemma_3_1
-- name    : MetricMSO.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:42:35.704751+00:00
-- url     : https://prove2.me/theorems/83813f0a-c415-4e27-9ef7-7c707ebca4b1
-- title:
--   Lemma 3.1 — a path is shortest iff a 1-Lipschitz integer potential increases along it
-- statement:
--   Let $P=v_0v_1\cdots v_r$ be a path in $G$ with $s=v_0$ and $t=v_r$. Then $P$ is a shortest $s$-$t$ path if and only if there is a map $\lambda:V(G)\to\mathbb Z$ with
--   $$|\lambda(u)-\lambda(v)|\le1\quad\text{for every }uv\in E(G),$$
--   $$\lambda(v_{i+1})=\lambda(v_i)+1\quad\text{for every }0\le i<r.$$
--
--   This is the integer form of the certificate, which the following statements replace by finite labels.
--
--   Differences from the source:
--   - encoding: the path P = v₀…v_r → a walk p with Walk.IsPath, r = p.length and vᵢ = p.getVert i; reason: the same object
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), Lemma 3.1, p.20 (PDF 22)

import Mathlib

namespace MetricMSO

/-- **Lemma 3.1.** Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863), p.20 (PDF 22): "Let P = v0v1 · · · vr be a
path in G, with s = v0 and t = vr. The following statements are equivalent. (a) P is a shortest s-t
path. (b) There exists a map λ: V(G) → Z such that |λ(u) − λ(v)| ≤ 1 for every uv ∈ E(G), (3)
λ(vi+1) = λ(vi) + 1 for every 0 ≤ i < r. (4)"

**Formalization Note** `P` is a walk with `Walk.IsPath`, `r` its length, `vᵢ` is `p.getVert i`.
"Shortest" is `p.length = G.dist s t`; `G.dist` is the true distance because `p` joins `s` and
`t`. -/
theorem lemma_3_1 {V : Type} [Fintype V] (G : SimpleGraph V) {s t : V} (p : G.Walk s t)
    (hp : p.IsPath) :
    p.length = G.dist s t ↔
      ∃ lam : V → ℤ, (∀ u v, G.Adj u v → |lam u - lam v| ≤ 1) ∧
        ∀ i, i < p.length → lam (p.getVert (i + 1)) = lam (p.getVert i) + 1 := by sorry

end MetricMSO
