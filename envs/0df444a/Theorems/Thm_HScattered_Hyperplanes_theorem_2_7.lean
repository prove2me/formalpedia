-- Prove2me | Theorems.Thm_HScattered_Hyperplanes_theorem_2_7
-- name    : HScattered.Hyperplanes.theorem_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:10.088991+00:00
-- url     : https://prove2.me/theorems/2cbca7ae-eeba-4c42-aa16-8f75ac6fdd69
-- title:
--   Theorem 2.7 — hyperplane intersections of a maximum h-scattered subspace of dimension rn/(h + 1)
-- statement:
--   Let $\mathbb F_q \subseteq \mathbb F_{q^n}$ be finite fields and $V = V(r,q^n)$ an $r$-dimensional $\mathbb F_{q^n}$-vector space. If $U$ is a maximum $h$-scattered $\mathbb F_q$-subspace of $V$ of dimension $rn/(h+1)$, then for every $(r-1)$-dimensional $\mathbb F_{q^n}$-subspace $W$ of $V$,
--   $$\frac{rn}{h+1} - n \;\le\; \dim_{\mathbb F_q}(U \cap W) \;\le\; \frac{rn}{h+1} - n + h .$$
--
--   For $h = 1$ this is Blokhuis–Lavrauw's theorem on scattered subspaces of dimension $rn/2$. The upper bound is what the paper's Delsarte-duality construction (§3) needs to show that the dual of such a subspace is again maximum scattered.
--
--   **Formalization Note** "Dimension $rn/(h+1)$" is $(h+1)\dim_{\mathbb F_q} U = rn$, with $r = \dim_{\mathbb F_{q^n}} V$ and $n = [\mathbb F_{q^n} : \mathbb F_q]$. Both inequalities are stated with $rn/(h+1)$ replaced by $\dim_{\mathbb F_q} U$ and $n$ moved across, i.e. $\dim U \le \dim(U\cap W) + n \le \dim U + h$, so no natural-number subtraction occurs. The range $0 < h < r$ is part of "$h$-scattered".
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 8, Theorem 2.7 (restated p. 18, proved in §5, pp. 18–24)

import Mathlib
import Definitions.Def_HScattered_Hyperplanes_IsHScattered

namespace HScattered.Hyperplanes

/-- Theorem 2.7 (arXiv:1906.10590v2, p. 8; proved in §5, pp. 18–24). Let `U` be a maximum
`h`-scattered `F`-subspace of `V = V(r, qⁿ)` (`r = finrank K V`, `n = finrank F K`) of dimension
`rn/(h + 1)`, i.e. `(h + 1) · dim_F U = r n`. Then every `(r − 1)`-dimensional `K`-subspace `W`
satisfies `rn/(h+1) − n ≤ dim_F (U ∩ W) ≤ rn/(h+1) − n + h`, written with `rn/(h+1) = dim_F U`
and the `n` moved to the other side (no natural-number subtraction). -/
theorem theorem_2_7 {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h : ℕ) (U : Submodule F V) (hU : IsMaximumHScattered F K h U)
    (hdim : (h + 1) * Module.finrank F U = Module.finrank K V * Module.finrank F K)
    (W : Submodule K V) (hW : Module.finrank K W = Module.finrank K V - 1) :
    Module.finrank F U ≤
        Module.finrank F ↥(W.restrictScalars F ⊓ U) + Module.finrank F K ∧
      Module.finrank F ↥(W.restrictScalars F ⊓ U) + Module.finrank F K ≤
        Module.finrank F U + h := by sorry

end HScattered.Hyperplanes
