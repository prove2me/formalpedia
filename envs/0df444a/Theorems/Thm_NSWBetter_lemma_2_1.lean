-- Prove2me | Theorems.Thm_NSWBetter_lemma_2_1
-- name    : NSWBetter.lemma_2_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T06:51:46.531782+00:00
-- url     : https://prove2.me/theorems/c7ca5085-fb2b-4c36-a902-55d96105bef7
-- title:
--   Lemma 2.1 — swapping $S_i$ and $S_j$ does not increase $v(X_i)v(X_j)$
-- statement:
--   Let all agents share the additive valuation $v\ge0$, and let $X_i,X_j$ be the (disjoint) bundles of two agents $i\ne j$ in an allocation. Let $S_i\subseteq X_i$ and $S_j\subseteq X_j$ with
--   $$v(S_j)\ge v(S_i),\qquad v(X_i\setminus S_i)\ge v(X_j\setminus S_j).$$
--   Swapping $S_i$ and $S_j$ gives $Y_i=(X_i\setminus S_i)\cup S_j$ and $Y_j=(X_j\setminus S_j)\cup S_i$. Then
--   $$v(Y_i)\,v(Y_j)\le v(X_i)\,v(X_j),$$
--   with equality if and only if $v(S_j)=v(S_i)$ or $v(X_i\setminus S_i)=v(X_j\setminus S_j)$.
--
--   This exchange step is used in the proofs of Lemma 3.6 and Lemma 4.2.
--
--   Differences from the source:
--   - encoding: an allocation $X$ and two agents $i,j$ → two disjoint bundles $X_i,X_j$ of goods; reason: the statement involves only these two bundles, and any two bundles of an allocation are disjoint
--   - encoding: valuation $v:2^G\to\mathbb R_{\ge0}$, additive → `v : Fin m → ℝ` with $v\ge0$ and bundle values as sums; reason: Lean convention; same instances
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Lemma 2.1, p.9

import Mathlib

namespace NSWBetter

/-- **Lemma 2.1 (swap lemma).**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Lemma 2.1, p.9: "Given a fair allocation instance where all agents have the same valuation function v, let X be an allocation and let i, j ∈ N be two agents. Let Si ⊆ Xi and Sj ⊆ Xj be two sets of goods such that v(Sj) ≥ v(Si) and v(Xi \ Si) ≥ v(Xj \ Sj). Let Y be an allocation constructed by starting at X and swapping the sets of goods Si and Sj; that is, Yi = (Xi \ Si) ∪ Sj and Yj = (Xj \ Sj) ∪ Si. Then, v(Yi)v(Yj) ≤ v(Xi)v(Xj). Moreover, equality holds if and only if v(Sj) = v(Si) or v(Xi \ Si) = v(Xj \ Sj)."

**Formalization Note.** Only the two bundles `X_i`, `X_j` of the allocation matter; they are disjoint sets of goods. The common additive valuation is `v : Fin m → ℝ`, `v ≥ 0`. -/
theorem lemma_2_1 {m : ℕ} (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g) (Xi Xj Si Sj : Finset (Fin m))
    (hdisj : Disjoint Xi Xj) (hSi : Si ⊆ Xi) (hSj : Sj ⊆ Xj)
    (h1 : ∑ g ∈ Si, v g ≤ ∑ g ∈ Sj, v g) (h2 : ∑ g ∈ Xj \ Sj, v g ≤ ∑ g ∈ Xi \ Si, v g) :
    (∑ g ∈ (Xi \ Si) ∪ Sj, v g) * (∑ g ∈ (Xj \ Sj) ∪ Si, v g) ≤
        (∑ g ∈ Xi, v g) * (∑ g ∈ Xj, v g) ∧
      ((∑ g ∈ (Xi \ Si) ∪ Sj, v g) * (∑ g ∈ (Xj \ Sj) ∪ Si, v g) =
          (∑ g ∈ Xi, v g) * (∑ g ∈ Xj, v g) ↔
        ∑ g ∈ Sj, v g = ∑ g ∈ Si, v g ∨ ∑ g ∈ Xi \ Si, v g = ∑ g ∈ Xj \ Sj, v g) := by sorry

end NSWBetter
