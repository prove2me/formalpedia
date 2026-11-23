-- Prove2me | Theorems.Thm_InconsistentDR_Shadow_Supplement_theorem_5_5
-- name    : InconsistentDR.Shadow.Supplement.theorem_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T05:13:48.067569+00:00
-- url     : https://prove2.me/theorems/935696ff-7424-47e7-9dfe-0680b3b6c2d0
-- title:
--   Theorem 5.5 (i)–(ix), p. 20 — Fejér monotonicity, boundedness and divergence of the Douglas–Rachford shadow sequences
-- statement:
--   Let $X$ be a real Hilbert space and let $A,B:X\rightrightarrows X$ be maximally monotone operators. Let $J_A=(\mathrm{Id}+A)^{-1}$ and $J_B=(\mathrm{Id}+B)^{-1}$ be their resolvents, let $R_A=2J_A-\mathrm{Id}$, and let
--
--   $$T=\mathrm{Id}-J_A+J_BR_A$$
--
--   be the Douglas–Rachford operator. Write $J_{A^{-1}}=\mathrm{Id}-J_A$. Let $D=\operatorname{dom}A-\operatorname{dom}B$ and $R=\operatorname{ran}A+\operatorname{ran}B$, and let $v=P_{\overline{\operatorname{ran}}(\mathrm{Id}-T)}(0)$ be the minimal displacement vector. The standing assumption (12) of the paper is in force:
--
--   $$\overline{\operatorname{ran}}(\mathrm{Id}-T)=\overline{D\cap R}=\overline D\cap\overline R .$$
--
--   Further, let $v_D=P_{\overline D}(0)$, $v_R=P_{\overline R}(0)$ and $J_{B^{-1}}=\mathrm{Id}-J_B$. For the normal problem $0\in -v+Ax+B(x-v)$ let $Z$ be the set of its solutions, let $K=\{k\mid\exists z,\ k\in -v+Az,\ -k\in B(z-v)\}$ be the set of its dual solutions, and let $\mathcal S=\{(z,k)\mid -k\in B(z-v),\ k\in -v+Az\}$ be its extended solution set. A sequence in $X\times X$ is Fejér monotone with respect to a set if its distance to each point of the set, in the norm $\|(a,b)\|^2=\|a\|^2+\|b\|^2$, never increases.
--
--   Suppose that $\operatorname{Fix}(v+T)\neq\varnothing$ and let $x\in X$. For $n\in\mathbb N$ put
--
--   $$p_n=J_AT^nx+nv_R,\qquad q_n=J_{A^{-1}}T^nx+nv_D .$$
--
--   Then the following hold.
--
--   1. (i) $(p_n,q_n)_{n\in\mathbb N}$ is Fejér monotone with respect to $\{(J_Ap,J_{A^{-1}}p)\mid p\in\operatorname{Fix}(v+T)\}$.
--
--   2. (ii) $(p_n,q_n)_{n\in\mathbb N}$ is bounded.
--
--   3. (iii) $(J_BR_AT^nx+nv_R,\;J_{B^{-1}}R_AT^nx-nv_D)_{n\in\mathbb N}$ is bounded.
--
--   4. (iv) $(p_n,-v+q_n)_{n\in\mathbb N}$, the translate of $(p_n,q_n)$ by $(0,-v)$, is Fejér monotone with respect to $\mathcal S$.
--
--   5. (v) $(J_AT^nx)_{n\in\mathbb N}$ is bounded if and only if $v_R=0$.
--
--   6. (vi) If $v_R\neq0$, then $\|J_AT^nx\|\to+\infty$.
--
--   7. (vii) $(J_{A^{-1}}T^nx)_{n\in\mathbb N}$ is bounded if and only if $v_D=0$.
--
--   8. (viii) If $v_D\neq0$, then $\|J_{A^{-1}}T^nx\|\to+\infty$.
--
--   9. (ix) If $A$ and $B$ are paramonotone, then $(p_n,-v+q_n)_{n\in\mathbb N}$ is Fejér monotone with respect to $Z\times K$. An operator $C$ is paramonotone if it is monotone and $u\in Cx$, $w\in Cy$, $\langle x-y,u-w\rangle=0$ imply $w\in Cx$ and $u\in Cy$.
--
--   The theorem describes both shadow sequences when the problem may be inconsistent: the primal shadow drifts along $-v_R$ and the dual shadow along $-v_D$, each is bounded exactly when its drift vanishes, and after the drift is removed their pair stays Fejér monotone.
--
--   **Formalization Note** The statement has all nine parts. Parts (ii) and (ix) also form the separately published theorem `InconsistentDR.Shadow.theorem_5_5`, whose binders are used here. Completeness of $X$, maximal monotonicity of $A$ and $B$ and assumption (12) are the standing hypotheses of the paper. Paramonotonicity is assumed in (ix) only.
--
--   Differences from the source:
--   - reading: the theorem supposes that $f\in\operatorname{Fix}(v+T)$ and then uses $f$ again as the running element of the set in (i) → the hypothesis is $\operatorname{Fix}(v+T)\neq\varnothing$, and in (i) the set contains the pair of every point $p$ of $\operatorname{Fix}(v+T)$; reason: the letter is bound twice on the page and the set in (i) ranges over all of $\operatorname{Fix}(v+T)$
--   - reading: the theorem says "let $n\in\mathbb N$" before statements about sequences indexed by $n$ → there is no free $n$, and each part concerns the whole sequence starting at $n=0$; reason: the printed $n$ is the index of the sequences
--   - encoding: the resolvents are defined by $J_A=(\mathrm{Id}+A)^{-1}$ and $J_B=(\mathrm{Id}+B)^{-1}$ → maps `JA`, `JB` satisfy $x-J_Ax\in A(J_Ax)$ and $x-J_Bx\in B(J_Bx)$ for every $x$; reason: for maximally monotone operators on a Hilbert space these maps exist and are unique (Minty), so they are the resolvents
--   - encoding: $J_{A^{-1}}$ and $J_{B^{-1}}$ are the resolvents of the operators $A^{-1}$ and $B^{-1}$ → `resInv JA` $=\mathrm{Id}-J_A$ and `resInv JB` $=\mathrm{Id}-J_B$; reason: the inverse resolvent identity (8) of the paper
--   - encoding: $v$, $v_D$, $v_R$ are the projections of $0$ onto three closures → they are least-norm points of those closures; reason: the closures are nonempty, closed and convex, so the least-norm points are these projections
--   - encoding: Fejér monotonicity in the Hilbert space $X\times X$ → `IsFejerPair`, the inequality between sums of squared norms of the components; reason: this is the squared Hilbert product norm, while the product type of Lean carries the sup norm
--   - encoding: boundedness of a sequence of pairs in (ii) and (iii) → boundedness of both coordinate sequences; reason: a sequence of pairs is bounded exactly when both coordinates are
--   - encoding: the dual solution set $K$ of (15) is written with inverses of operators → `solK` $=\{k\mid\exists z,\ k+v\in Az,\ -k\in B(z-v)\}$; reason: this is (15) unfolded
-- source:
--   Bauschke & Moursi, On the Douglas–Rachford algorithm for solving possibly inconsistent optimization problems, arXiv:2106.11547v1 (22 Jun 2021), p. 20, Theorem 5.5 (i)–(ix), with (4a), (4b), (5), pp. 2–3, (8), p. 5, (12), (14), (15), p. 6, and (18) and footnote 1, p. 7

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_InconsistentDR_Shadow_Operators

namespace InconsistentDR.Shadow.Supplement

open Filter ThreeOpSplitting.Convergence

/-- Theorem 5.5, p. 20, all nine parts, under (12), when `Fix(v + T) ≠ ∅`, for every starting
point `x`. Write `pₙ = J_A Tⁿx + n v_R` and `qₙ = J_{A⁻¹} Tⁿx + n v_D`:
(i) `(pₙ, qₙ)ₙ` is Fejér monotone w.r.t. `{(J_A p, J_{A⁻¹} p) | p ∈ Fix(v + T)}`;
(ii) `(pₙ, qₙ)ₙ` is bounded;
(iii) `(J_B R_A Tⁿx + n v_R, J_{B⁻¹} R_A Tⁿx − n v_D)ₙ` is bounded;
(iv) `((0, −v) + (pₙ, qₙ))ₙ` is Fejér monotone w.r.t. `S`;
(v) `(J_A Tⁿx)ₙ` is bounded iff `v_R = 0`; (vi) if `v_R ≠ 0` then `‖J_A Tⁿx‖ → +∞`;
(vii) `(J_{A⁻¹} Tⁿx)ₙ` is bounded iff `v_D = 0`; (viii) if `v_D ≠ 0` then `‖J_{A⁻¹} Tⁿx‖ → +∞`;
(ix) if `A`, `B` are paramonotone, `((0, −v) + (pₙ, qₙ))ₙ` is Fejér monotone w.r.t. `Z × K`.
Fejér monotonicity is for the Hilbert norm of `X × X`. -/
theorem theorem_5_5 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (A B : X → Set X) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (JA JB : X → X) (hJA : IsResolvent 1 A JA) (hJB : IsResolvent 1 B JB)
    (v vD vR : X)
    (hv : IsMinNormPt (closure (Set.range fun x => x - drT JA JB x)) v)
    (hvD : IsMinNormPt (closure (setD A B)) vD) (hvR : IsMinNormPt (closure (setR A B)) vR)
    (h12 : Standing12 A B JA JB)
    (hfix : (FixSet fun y => v + drT JA JB y).Nonempty) (x : X) :
    -- (i)
    IsFejerPair (fun n => JA ((drT JA JB)^[n] x) + (n : ℝ) • vR)
      (fun n => resInv JA ((drT JA JB)^[n] x) + (n : ℝ) • vD)
      ((fun p => (JA p, resInv JA p)) '' FixSet (fun y => v + drT JA JB y)) ∧
    -- (ii)
    (Bornology.IsBounded (Set.range fun n : ℕ => JA ((drT JA JB)^[n] x) + (n : ℝ) • vR) ∧
      Bornology.IsBounded
        (Set.range fun n : ℕ => resInv JA ((drT JA JB)^[n] x) + (n : ℝ) • vD)) ∧
    -- (iii)
    (Bornology.IsBounded
        (Set.range fun n : ℕ => JB (refl JA ((drT JA JB)^[n] x)) + (n : ℝ) • vR) ∧
      Bornology.IsBounded
        (Set.range fun n : ℕ => resInv JB (refl JA ((drT JA JB)^[n] x)) - (n : ℝ) • vD)) ∧
    -- (iv)
    IsFejerPair (fun n => JA ((drT JA JB)^[n] x) + (n : ℝ) • vR)
      (fun n => -v + (resInv JA ((drT JA JB)^[n] x) + (n : ℝ) • vD))
      (solS A B v) ∧
    -- (v)
    (Bornology.IsBounded (Set.range fun n : ℕ => JA ((drT JA JB)^[n] x)) ↔ vR = 0) ∧
    -- (vi)
    (vR ≠ 0 → Tendsto (fun n : ℕ => ‖JA ((drT JA JB)^[n] x)‖) atTop atTop) ∧
    -- (vii)
    (Bornology.IsBounded (Set.range fun n : ℕ => resInv JA ((drT JA JB)^[n] x)) ↔ vD = 0) ∧
    -- (viii)
    (vD ≠ 0 → Tendsto (fun n : ℕ => ‖resInv JA ((drT JA JB)^[n] x)‖) atTop atTop) ∧
    -- (ix)
    (IsParamonotone A → IsParamonotone B →
      IsFejerPair (fun n => JA ((drT JA JB)^[n] x) + (n : ℝ) • vR)
        (fun n => -v + (resInv JA ((drT JA JB)^[n] x) + (n : ℝ) • vD))
        (solZ A B v ×ˢ solK A B v)) := by sorry

end InconsistentDR.Shadow.Supplement
