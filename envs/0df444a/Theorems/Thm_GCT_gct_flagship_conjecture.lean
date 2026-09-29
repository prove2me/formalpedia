-- Prove2me | Theorems.Thm_GCT_gct_flagship_conjecture
-- name    : GCT.gct_flagship_conjecture
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T16:35:12.080242+00:00
-- url     : https://prove2.me/theorems/498980f7-6512-4a79-9796-68140c55c691
-- title:
--   GCT flagship conjecture: $\overline{\mathrm{dc}}(\mathrm{perm}_m)$ grows superpolynomially
-- statement:
--   **The flagship conjecture of Geometric Complexity Theory** (Mulmuley–Sohoni). Let $W = \mathbb{C}^{n^2}$, let $\det_n \in S^n W$ be the determinant of an $n \times n$ matrix of variables, and let $\mathrm{perm}_m$ be the permanent of an $m \times m$ matrix of variables. Writing $\ell$ for an auxiliary linear coordinate and fixing a linear inclusion $\mathbb{C}^{m^2 + 1} \hookrightarrow W$, the padded permanent $\ell^{\,n-m}\mathrm{perm}_m$ lies in $S^n W$, and one sets
--
--   $$\mathrm{Det}_n = \overline{GL(W) \cdot [\det_n]}, \qquad \mathrm{Perm}^m_n = \overline{GL(W) \cdot [\ell^{\,n-m}\mathrm{perm}_m]} \;\subset\; \mathbb{P}S^n W.$$
--
--   The border determinantal complexity $\overline{\mathrm{dc}}(\mathrm{perm}_m)$ is the least $n$ with $[\ell^{\,n-m}\mathrm{perm}_m] \in \mathrm{Det}_n$, equivalently the least $n$ with $\mathrm{Perm}^m_n \subseteq \mathrm{Det}_n$. The conjecture asserts that $\overline{\mathrm{dc}}(\mathrm{perm}_m)$ grows faster than any polynomial in $m$: for every exponent $c$ there is an $m_0$ such that $\overline{\mathrm{dc}}(\mathrm{perm}_m) > m^c$ for all $m \ge m_0$. Equivalently, in the formulation of Landsberg's survey: for $n = m^c$ with $c$ constant and $m$ sufficiently large, $\mathrm{Perm}^m_n \not\subseteq \mathrm{Det}_n$. This is the Zariski-closed strengthening of Valiant's conjecture $\mathbf{VP}_{ws} \ne \mathbf{VNP}$, and it is open.
-- source:
--   J. M. Landsberg, *Geometry and Complexity Theory*, Cambridge Studies in Advanced Mathematics 169, CUP 2017, DOI 10.1017/9781108183192, p. 16, Definition 1.2.5.1 and Conjecture 1.2.5.2 (Mulmuley–Sohoni [MS01]); and J. M. Landsberg, *Geometric Complexity Theory: an introduction for geometers*, arXiv:1305.7387v3, https://arxiv.org/abs/1305.7387, p. 3, Conjecture 2.1, with the restatement on p. 4 that it says dc-bar(perm_m) grows faster than any polynomial in m.

import Definitions.Def_GCT_determinantal_complexity

namespace GCT

theorem gct_flagship_conjecture :
    ∀ c : ℕ, ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → m ^ c < dcBar m := by sorry

end GCT
