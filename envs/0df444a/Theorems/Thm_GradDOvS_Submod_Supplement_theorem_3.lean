-- Prove2me | Theorems.Thm_GradDOvS_Submod_Supplement_theorem_3
-- name    : GradDOvS.Submod.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:18:59.585803+00:00
-- url     : https://prove2.me/theorems/22f414d7-e5f4-49f0-8c09-66b04529f69d
-- title:
--   Theorem 3, p. 22 (corrected: local coordinates x − y in f̃_y) — the piecewise Lovász extension (7) of an L♮-convex function is well defined and convex on [1, N]^d
-- statement:
--   Let $d \ge 1$ and $N \ge 2$, and let $f : \mathcal X = [N]^d \to \mathbb R$ be L♮-convex (discrete midpoint convexity, Definition 3). For $y \in [N-1]^d$ let $\mathcal C_y = y + [0,1]^d$, and for $x \in \mathcal C_y$ and a consistent permutation $\alpha$ of $x - y$ let
--   $$\tilde f_y(x) = f(S^{x,0}) + \sum_{i=1}^{d}\big[f(S^{x,i}) - f(S^{x,i-1})\big]\,(x-y)_{\alpha(i)}, \qquad S^{x,i} = y + \sum_{j=1}^{i} e_{\alpha(j)} .$$
--   Let $\tilde f$ be the extension (7), $\tilde f(x) = \tilde f_y(x)$ for a cube $\mathcal C_y \ni x$. Then:
--
--   1. **(well-defined)** every $x \in [1,N]^d$ lies in some cube $\mathcal C_y$ with $y \in [N-1]^d$, and for every such cube and every consistent permutation $\alpha$ of $x - y$,
--   $$\tilde f(x) = \tilde f_y(x);$$
--   in particular the value of (7) does not depend on the cube or on the permutation chosen;
--   2. **(convex)** $\tilde f$ is convex on $\operatorname{conv}(\mathcal X) = [1,N]^d$.
--
--   This is the convex extension that lets the subgradient method of §3 run on general boxes $[N]^d$ (Theorem 4) and that underlies the weak sharp minimum characterization of Theorem EC.3.
--
--   **Formalization Note** $\tilde f$ is computed with a canonical cube and the canonical consistent permutation, and clause 1 compares it with every admissible choice, so well-definedness is a real claim and not a consequence of the definition. Indices are 0-based.
--
--   Differences from the source:
--   - correction: the display of $\tilde f_y$ on p. 21 multiplies by $x_{\alpha(i)}$ → the local coordinate $(x-y)_{\alpha(i)}$; reason: typo, the proof (EC.13), p. ec12 (PDF 50), uses $x - y$; with the printed $x_{\alpha(i)}$ the extension is not well defined (for $d = 1$, $N = 3$, $x = 2$ the cube $\mathcal C_1$ gives $f(1) + 2(f(2)-f(1))$ and $\mathcal C_2$ gives $f(2) + 2(f(3)-f(2))$, which differ for $f = (0,1,3)$)
--   - reading: convex on $\mathcal X$ → convex on $[1,N]^d$; reason: $\mathcal X$ is discrete and p. 21 announces "a convex function on $\operatorname{conv}(\mathcal X) = [1,N]^d$"
--   - reading: well-defined → every point of $[1,N]^d$ lies in some $\mathcal C_y$, and every local formula $\tilde f_y(x)$ with every consistent permutation of $x - y$ equals $\tilde f(x)$; reason: (7) quantifies over every admissible $y$, and the proof on p. ec12 states exactly this agreement
--   - encoding: $f : \mathcal X \to \mathbb R$ with the standing assumptions of §4 → $f : \mathbb Z^d \to \mathbb R$, only its values on $[N]^d$ used, with hypotheses $d \ge 1$, $N \ge 2$ (Assumption 3) and L♮-convexity on $[N]^d$ (Assumption 2); reason: Lean convention for a function on a subset; the hypotheses are the section's standing assumptions
-- source:
--   Zhang, Zheng & Lavaei, arXiv:2010.16250v3, p. 22, Theorem 3, with (7) and pp. 21–22; proof p. ec12 (PDF 50), (EC.13)

import Mathlib
import Definitions.Def_GradDOvS_Submod_Supplement_ConvexExt

namespace GradDOvS.Submod.Supplement

/-- Theorem 3, p. 22: for an L♮-convex `f` on `X = [N]^d`, the piecewise Lovász extension `f̃` of (7)
is well defined — every point of `[1, N]^d` lies in some hypercube `C_y`, and for every hypercube
`C_y` containing `x` and every consistent permutation `α` of `x - y` the local formula `f̃_y(x)` equals
`f̃(x)` — and `f̃` is convex on `conv(X) = [1, N]^d`. -/
theorem theorem_3 (d N : ℕ) (hd : 1 ≤ d) (hN : 2 ≤ N) (f : (Fin d → ℤ) → ℝ)
    (hf : LNatConvexOn d N f) :
    (∀ x ∈ realBox d N, ∃ y ∈ cubeBases d N, x ∈ cube y) ∧
    (∀ y ∈ cubeBases d N, ∀ x ∈ cube y, ∀ α : Equiv.Perm (Fin d),
        IsConsistentPerm (fun i => x i - ((y i : ℤ) : ℝ)) α →
          convexExt N f x = localLovasz f y α x) ∧
    ConvexOn ℝ (realBox d N) (convexExt N f) := by sorry

end GradDOvS.Submod.Supplement
