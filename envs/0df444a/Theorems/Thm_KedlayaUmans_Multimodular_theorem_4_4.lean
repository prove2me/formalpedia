-- Prove2me | Theorems.Thm_KedlayaUmans_Multimodular_theorem_4_4
-- name    : KedlayaUmans.Multimodular.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:48:07.635863+00:00
-- url     : https://prove2.me/theorems/a386c15f-ae04-4974-a6b0-aa6a940f7182
-- title:
--   Theorem 4.4 — Algorithm MULTIMODULAR-FOR-EXTENSION-RING returns $f(\alpha_i)$ (correctness)
-- statement:
--   Let $r \ge 1$, let $E(Z) \in (\mathbb Z/r\mathbb Z)[Z]$ be monic of degree $e \ge 1$, and let $R = (\mathbb Z/r\mathbb Z)[Z]/(E(Z))$. Let $m \ge 1$, $d \ge 2$ and $t \ge 1$ be integers, let $f \in R[X_0,\dots,X_{m-1}]$ have degree at most $d-1$ in each variable, and let $\alpha \in R^m$. Then Algorithm MULTIMODULAR-FOR-EXTENSION-RING with degree parameter $d$ and $t$ rounds returns the value of $f$ at $\alpha$:
--   $$\mathrm{MULTIMODULAR\text{-}FOR\text{-}EXTENSION\text{-}RING}_d(f, \alpha, t) = f(\alpha).$$
--
--   This is the correctness half of Theorem 4.4. It makes the multimodular evaluation algorithm available over every ring $(\mathbb Z/r\mathbb Z)[Z]/(E(Z))$, in particular every finite field. That is the evaluation step the paper's modular-composition and polynomial-factorization algorithms rely on.
--
--   **Formalization Note** The running-time half of Theorem 4.4 is not formalized. The hypotheses $d \ge 2$, $m \ge 1$ and $e \ge 1$ are implicit in the paper. $d \ge 2$ and $m \ge 1$ are needed: with $m = 0$ the degree bound $(e-1)dm$ is $0$ while a constant $f$ can have degree up to $e-1$. The $N$ evaluation points are treated independently, so the statement for one arbitrary point covers all $N$. $r'$ is $M^{(e-1)dm+1}$ as on p. 15.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (version of Aug. 31, 2008), p. 15, Theorem 4.4

import Mathlib
import Definitions.Def_KedlayaUmans_Multimodular_Algorithm
import Definitions.Def_KedlayaUmans_Multimodular_ExtensionRing

namespace KedlayaUmans.Multimodular

open Polynomial

/-- **Theorem 4.4** (correctness half). Over `R = (ℤ/rℤ)[Z]/(E(Z))` with `E` monic of degree
`e ≥ 1`, Algorithm MULTIMODULAR-FOR-EXTENSION-RING with `t ≥ 1` rounds returns `f(α)` for every
`f ∈ R[X₀, …, X_{m-1}]` of degree at most `d - 1` in each variable and every `α ∈ R^m`. -/
theorem theorem_4_4 {r m : ℕ} [NeZero r] (d t : ℕ) (ht : 1 ≤ t) (hd : 2 ≤ d) (hm : 1 ≤ m)
    (E : (ZMod r)[X]) (hE : E.Monic) (he : 1 ≤ E.natDegree)
    (f : MvPolynomial (Fin m) (AdjoinRoot E)) (hf : ∀ i, f.degreeOf i ≤ d - 1)
    (α : Fin m → AdjoinRoot E) :
    multimodularExt d t hE f α = MvPolynomial.eval α f := by sorry

end KedlayaUmans.Multimodular
