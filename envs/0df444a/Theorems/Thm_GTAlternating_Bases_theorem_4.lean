-- Prove2me | Theorems.Thm_GTAlternating_Bases_theorem_4
-- name    : GTAlternating.Bases.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:17.038978+00:00
-- url     : https://prove2.me/theorems/4d80fecd-2f70-485b-b2b6-9fbed19ffba6
-- title:
--   Theorem 4 (Main Theorem), p. 14 — each u_α̲ is a Gelfand–Tsetlin vector of V_α, and class representatives give a Gelfand–Tsetlin basis
-- statement:
--   Let $n \ge 2$ and $\alpha \in \tilde\Theta(n)$.
--
--   1. For every path $\underline\alpha = (\alpha^{(2)},\dots,\alpha^{(n)}) \in \tilde{\mathcal S}(\alpha)$, the vector $u_{\underline\alpha}$ of Definition 2 is a Gelfand–Tsetlin basis vector of $V_\alpha$ corresponding to the geodesic $\Gamma(\underline\alpha)$: it is nonzero, lies in $V_\alpha$, and for every $k = 2,\dots,n-1$ lies in the $A_k$-isotypic subspace of type $V_{\alpha^{(k)}}$.
--   2. Let $R \subseteq \tilde{\mathcal S}(\alpha)$ be a set of paths, all ending in $\alpha^{(n)} = \alpha$, containing exactly one member of each $\sim$-class of such paths. Then $\{u_{\underline\alpha} \mid \underline\alpha \in R\}$ is linearly independent and spans $V_\alpha$:
--   $$V_\alpha = \bigoplus_{\underline\alpha \in R} \mathbb C\, u_{\underline\alpha}.$$
--
--   This is the main result of the paper: the explicitly computable vectors $u_{\underline\alpha}$, built from Young's orthogonal basis of $V_\lambda$ and the normalised associator $\varphi_\lambda$, form a Gelfand–Tsetlin basis of each irreducible representation of $A_n$.
--
--   **Formalization Note.** A path is stored top-down as $\alpha$ with the list $[\alpha^{(n-1)},\dots,\alpha^{(2)}]$, so a representative set $R$ is a set of such lists; two paths ending at $\alpha$ are equivalent iff their lists agree entrywise up to $\sim$ (Remark 3). The Gelfand–Tsetlin predicate is intrinsic: isotypic subspaces are sums of images of all $A_k$-equivariant maps, $A_k$-equivariance being commutation with the generators $s_is_j$, $i,j\le k-1$, of $A_k$ (equivalent to $A_k$-equivariance because Young's formulas define a representation, [5, Theorem 2.1]). $n \ge 2$ is the paper's: paths start at $\tilde\Theta(2)$. Labels and tableau entries are 0-based in Lean.
-- source:
--   Geetha, Prasad, Comparison of Gelfand-Tsetlin bases for alternating and symmetric groups, arXiv:1606.04424v2, p. 14, Theorem 4 (Main Theorem), with Remark 3

import Mathlib
import Definitions.Def_GTAlternating_Bases_Model

namespace GTAlternating.Bases

theorem theorem_4 (n : ℕ) (hn : 2 ≤ n) (a : Label) (ha : a.size = n) :
    (∀ p : List Label, IsPath a p → IsGTVector a p (uVec a p)) ∧
    (∀ R : Set (List Label), (∀ p ∈ R, IsPath a p) →
      (∀ q, IsPath a q → ∃! p, p ∈ R ∧ List.Forall₂ Label.Equiv p q) →
      LinearIndependent ℂ (fun p : R => uVec a p.1) ∧
      Submodule.span ℂ (Set.range (fun p : R => uVec a p.1)) = a.space) := by sorry

end GTAlternating.Bases
