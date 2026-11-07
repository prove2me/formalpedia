-- Prove2me | Theorems.Thm_MetricMSO_lemma_3_4
-- name    : MetricMSO.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:42:48.80729+00:00
-- url     : https://prove2.me/theorems/e62e397c-aa32-448c-a4da-94583a5a29ce
-- title:
--   Lemma 3.4 — integer lift of an admissible $\mathbb Z_M$-labeling
-- statement:
--   Let $M\ge3$ satisfy $M>\mathrm{cbl}(G)$ and let $c:V(G)\to\mathbb Z_M$ be an admissible labeling. Then there is a map $\lambda:V(G)\to\mathbb Z$ such that
--
--   1. $\lambda(v)\equiv c(v)\pmod M$ for every vertex $v$, and
--   2. for every pair of adjacent vertices $u,v$, the difference $\lambda(v)-\lambda(u)$ is the unique integer in $\{-1,0,1\}$ congruent to $c(v)-c(u)$ modulo $M$.
--
--   Such a $\lambda$ is called an integer lift of $c$.
--
--   Differences from the source:
--   - encoding: the unique integer in {−1, 0, 1} congruent to c(v) − c(u) → membership in {−1, 0, 1} together with the congruence; reason: for M ≥ 3 such an integer is unique, so the two say the same
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), Lemma 3.4, p.22 (PDF 24)

import Mathlib
import Definitions.Def_MetricMSO_cbl
import Definitions.Def_MetricMSO_Admissible

namespace MetricMSO

/-- **Lemma 3.4 (integer lift).** Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863), p.22 (PDF 24): "Let M ≥ 3
satisfy M > cbl(G), and let c: V(G) → ZM be an admissible labeling. There exists a map λ: V(G) → Z
such that (i) λ(v) ≡ c(v) (mod M) for every v ∈ V(G), and (ii) for every pair of adjacent vertices
u, v, the difference λ(v) − λ(u) is the unique integer in {−1, 0, 1} congruent to c(v) − c(u) modulo
M."

**Formalization Note** Clause (ii) is stated as membership in `{−1, 0, 1}` together with the
congruence; uniqueness of such an integer is automatic for `M ≥ 3`. -/
theorem lemma_3_4 {V : Type} [Fintype V] (G : SimpleGraph V) (M : ℕ) (hM : 3 ≤ M)
    (hcbl : cbl G < M) (c : V → ZMod M) (hc : Admissible G c) :
    ∃ lam : V → ℤ, (∀ v, ((lam v : ℤ) : ZMod M) = c v) ∧
      ∀ u v, G.Adj u v → lam v - lam u ∈ ({-1, 0, 1} : Set ℤ) ∧
        ((lam v - lam u : ℤ) : ZMod M) = c v - c u := by sorry

end MetricMSO
