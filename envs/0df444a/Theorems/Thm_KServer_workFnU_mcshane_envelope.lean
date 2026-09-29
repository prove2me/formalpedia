-- Prove2me | Theorems.Thm_KServer_workFnU_mcshane_envelope
-- name    : KServer.workFnU_mcshane_envelope
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T05:54:30.18583+00:00
-- url     : https://prove2.me/theorems/55ecda2c-76ad-44dc-93a7-547c423bd8cf
-- title:
--   The extension work function is the McShane envelope of the original
-- statement:
--   Let a $k$-server instance live in a metric space $M$ with all distances bounded by $\Delta > 0$, and view it inside the antipodal extension $M \cup \bar M$. Write $w$ for the work function on $M$ and $w^{\mathrm{ext}}$ for the work function of the same instance computed in the extension. Then at **every** configuration $Z$ of the extension --- including configurations occupying antipodes ---
--
--   $$w^{\mathrm{ext}}(Z) \;=\; \min_{X \subseteq M} \bigl( w(X) + d(X, Z) \bigr),$$
--
--   the minimum being over configurations of original points, and attained. In words: $w^{\mathrm{ext}}$ is the **McShane--Lipschitz envelope** of $w$ --- the largest $1$-Lipschitz extension of $w$ from $M$-configurations to extension configurations. The formal statement gives the two halves separately: the upper bound for every $X$, and an $X$ attaining equality.
--
--   ## Role
--
--   The Coester--Koutsoupias potential is a sum of work-function values at configurations that mix original points with antipodes, evaluated in the extension. Every manipulation of such values that goes beyond formal Lipschitz bounds needs to know what they *are* in terms of the original instance, and this theorem is the answer: a work-function value at an antipodal configuration is a minimum, over original configurations, of original work-function values plus distances.
--
--   Two consequences drive the tree analysis. First, combined with the antipode identity $d(u, \bar y) = 2\Delta' - d(u, y)$, it converts values at antipodal configurations into **dual minima**: e.g. $w^{\mathrm{ext}}(\bar y^k) = 2k\Delta' + \min_{X \subseteq M}(w(X) - d(X, y^k))$, and crucially the minimum ranges over *original* configurations --- which is what licenses applying tree properties of the metric (the four-point condition holds for original points, not for antipodes) to the minimisers. This is the unstated step behind the expansion "$w(\bar y^k) = w(a_1 \dots a_{k-1} r) + \dots$ for some $a_i \in V$" in the tree section of Coester--Koutsoupias. Second, with $Z$ itself an original configuration it recovers the fact that the extension changes no original value, so the envelope description is a strict generalisation of the restriction theorem.
--
--   ## About the proof
--
--   The upper bound is $1$-Lipschitzness in the extension plus the restriction theorem. The attained lower bound is an induction along the request sequence. The recurrence resolves $Z$ through a configuration $Y_0$ covering the new request; the inductive hypothesis expresses $w^{\mathrm{ext}}$ at $Y_0$ through some original $X$; and a **surgery** step replaces every antipodal coordinate of $Y_0$ by the corresponding coordinate of $X$, the per-coordinate triangle inequality $d(x, \bar b) + d(\bar b, z) \ge d(x, z)$ showing the replacement only helps. The surgered configuration is original, still covers the request (requests are original points), and the original recurrence closes the induction.
--
--   ## Formalization note
--
--   The extension is `antipodalExtension M Δ hΔ0 hΔ` on the sum type $M \oplus M$; original points are embedded by `Sum.inl`, and $d(X,Z)$ is `moveCost` of the embedded configuration. The statement is for `workFnU`; no finiteness of $M$ is assumed --- attainment comes from the induction, not from compactness.
-- source:
--   The unstated structural step behind the tree and multi-ray analyses of C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021, arXiv:2102.10474 (e.g. the expansion of w(ȳ^k) through configurations of original points in Lemma 26); the envelope description of Lipschitz extension is McShane's.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension

namespace KServer

theorem workFnU_mcshane_envelope (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] (Δ : ℝ)
    (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ)
    (C₀ : Config k M) (σ : List M) (Z : Config k (M ⊕ M)) :
    (∀ X : Config k M,
      @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) Z
        ≤ workFnU C₀ σ X
          + @moveCost k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun i => Sum.inl (X i)) Z)
    ∧ ∃ X : Config k M,
      @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) Z
        = workFnU C₀ σ X
          + @moveCost k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun i => Sum.inl (X i)) Z := by sorry

end KServer
