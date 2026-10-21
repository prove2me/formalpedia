-- Prove2me | Theorems.Thm_InconsistentDR_Shadow_lemma_4_1
-- name    : InconsistentDR.Shadow.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:23.15388+00:00
-- url     : https://prove2.me/theorems/93740b8a-8f92-42b4-a6f0-f71e4fb4029b
-- title:
--   Lemma 4.1, p. 12 — on Fix(v + T): T f = f − v, J_A T f = J_A f − v_R, J_{A⁻¹}T f = J_{A⁻¹} f − v_D, (37); v ∈ ran(Id − T) ⇔ Fix(v + T) ≠ ∅
-- statement:
--   Throughout, $X$ is a real Hilbert space, $A, B : X \rightrightarrows X$ are maximally monotone, $J_A = (\mathrm{Id}+A)^{-1}$ and $J_B$ are their resolvents, $R_A = 2J_A - \mathrm{Id}$, $J_{A^{-1}} = \mathrm{Id} - J_A$ and $J_{B^{-1}} = \mathrm{Id} - J_B$, and
--   $$T = \mathrm{Id} - J_A + J_B R_A$$
--   is the Douglas–Rachford operator. The vectors $v = P_{\overline{\operatorname{ran}}(\mathrm{Id}-T)}(0)$, $v_D = P_{\overline{D}}(0)$ and $v_R = P_{\overline{R}}(0)$ are the projections of $0$ onto the closures of $\operatorname{ran}(\mathrm{Id}-T)$, $D = \operatorname{dom}A - \operatorname{dom}B$ and $R = \operatorname{ran}A + \operatorname{ran}B$, and the standing assumption (12) of the paper is in force:
--   $$\overline{\operatorname{ran}}(\mathrm{Id}-T) = \overline{D\cap R} = \overline{D}\cap\overline{R}.$$
--
--   Then:
--   1. Let $p \in \operatorname{Fix}(v + T)$, i.e. $p = v + Tp$. Then
--   $$Tp = p - v,\qquad J_A T p = J_A p - v_R,\qquad J_{A^{-1}} T p = J_{A^{-1}} p - v_D,$$
--   and
--   $$\langle J_A p - J_A T p,\ J_{A^{-1}} p - J_{A^{-1}} T p\rangle = \langle J_B R_A p - J_B R_A T p,\ J_{B^{-1}} R_A p - J_{B^{-1}} R_A T p\rangle = 0 .$$
--   2. $v \in \operatorname{ran}(\mathrm{Id} - T)$ if and only if $\operatorname{Fix}(v + T) \neq \varnothing$, and in that case $(v_D, v_R) \in D \times R$.
--
--   On a point of $\operatorname{Fix}(v+T)$ the operator $T$ acts as the translation by $-v$, and its two shadows move by $-v_R$ and $-v_D$.
--
--   **Formalization Note** The resolvents are maps `JA JB : X → X` characterized by `IsResolvent 1 A JA` ($x - J_A x \in A(J_A x)$ for every $x$, which is $J_A = (\mathrm{Id}+A)^{-1}$; for maximally monotone $A$ such a map exists and is unique). $J_{A^{-1}}$ is written `resInv JA` $= \mathrm{Id} - J_A$, by the inverse resolvent identity (8). The projections $v, v_D, v_R$ are encoded as least-norm points of the respective closures (these closures are nonempty, closed and convex, so the least-norm point is the projection of $0$). The standing assumption (12) of p. 6 is an explicit hypothesis, and `CompleteSpace X` makes the inner product space a Hilbert space. The paper calls the fixed point $f$; it is named $p$ here.
-- source:
--   Bauschke & Moursi, On the Douglas–Rachford algorithm for solving possibly inconsistent optimization problems, arXiv:2106.11547v1 (22 Jun 2021), p. 12, Lemma 4.1, (36a)–(36c), (37a)–(37b)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_InconsistentDR_Shadow_Operators

namespace InconsistentDR.Shadow

open scoped InnerProductSpace
open ThreeOpSplitting.Convergence

/-- Lemma 4.1, p. 12, under (12). (i) For a point `p ∈ Fix(v + T)` (the paper's `f`):
(36a) `T p = p − v`, (36b) `J_A T p = J_A p − v_R`, (36c) `J_{A⁻¹} T p = J_{A⁻¹} p − v_D`, and
(37a)–(37b). (ii) `v ∈ ran(Id − T) ⇔ Fix(v + T) ≠ ∅ ⇒ (v_D, v_R) ∈ D × R`. -/
theorem lemma_4_1 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (A B : X → Set X) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (JA JB : X → X) (hJA : IsResolvent 1 A JA) (hJB : IsResolvent 1 B JB)
    (v vD vR : X)
    (hv : IsMinNormPt (closure (Set.range fun x => x - drT JA JB x)) v)
    (hvD : IsMinNormPt (closure (setD A B)) vD) (hvR : IsMinNormPt (closure (setR A B)) vR)
    (h12 : Standing12 A B JA JB) :
    (∀ p ∈ FixSet (fun y => v + drT JA JB y),
      drT JA JB p = p - v ∧
      JA (drT JA JB p) = JA p - vR ∧
      resInv JA (drT JA JB p) = resInv JA p - vD ∧
      ⟪JA p - JA (drT JA JB p), resInv JA p - resInv JA (drT JA JB p)⟫_ℝ =
        ⟪JB (refl JA p) - JB (refl JA (drT JA JB p)),
          resInv JB (refl JA p) - resInv JB (refl JA (drT JA JB p))⟫_ℝ ∧
      ⟪JA p - JA (drT JA JB p), resInv JA p - resInv JA (drT JA JB p)⟫_ℝ = 0) ∧
    ((v ∈ Set.range fun x => x - drT JA JB x) ↔
      (FixSet fun y => v + drT JA JB y).Nonempty) ∧
    ((FixSet fun y => v + drT JA JB y).Nonempty → vD ∈ setD A B ∧ vR ∈ setR A B) := by sorry

end InconsistentDR.Shadow
