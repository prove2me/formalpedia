-- Prove2me | Theorems.Thm_MatrixLeeSidford_Supplement_theorem_9_6
-- name    : MatrixLeeSidford.Supplement.theorem_9_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T15:19:47.621742+00:00
-- url     : https://prove2.me/theorems/e0f56ecf-52c5-41c7-8cc1-981ce25788a9
-- title:
--   Theorem 9.6 — centering with G-steps: every query of Center is valid and the call returns $y$ with $\lambda_c(y)\le\delta_c$
-- statement:
--   Work in the setting of Part II: $1\le m\le n$, $A_1,\dots,A_m,C\in\mathbb S^n$ with $\Omega=\{y:S(y)\succ0\}\neq\emptyset$, the $A_i$ linearly independent and $\bigcap_i\ker A_i=\{0\}$; $F=\alpha\Phi_p$ is the matrix Lee–Sidford barrier with $s=2\lceil\log(2mn)\rceil$ and $\alpha=10^6s^2$. Use the parameters (8.10)–(8.11),
--   $$
--   \delta_c=\tfrac1{100},\ \mu=\tfrac18,\ e_0=\tfrac1{1600},\ \varepsilon_g=\tfrac{e_0}{\sqrt{32s}},\ E=\tfrac{\delta_c^2}{16},\ d_0=0.0054,\ \gamma_G=\tfrac1{1000s},\ \gamma_y=\tfrac{c_y}s,\ \eta_w=\tfrac{c_w}s,\ \eta=\tfrac{\eta_0}{\alpha s^2},\ \tau=\tfrac{\sqrt\eta}{32},
--   $$
--   $$
--   N_G=\Big\lceil\tfrac{16}{\gamma_G}\log\tfrac{4\eta_w}{\eta}\Big\rceil,\qquad N_y=\Big\lceil\tfrac1{\mu\gamma_y}\log\tfrac{4d_0}{E}\Big\rceil,\qquad N_c=(N_G+1)N_y,
--   $$
--   where the positive constants $c_w,\eta_0,c_y$ satisfy $c_w\le c_{\mathrm{pert}}/4$, $\eta\le\eta_w/16$, $c_y\le1/200$ and
--   $$
--   C_{\mathrm{pert}}\sqrt{\alpha s\eta}\le\frac{\varepsilon_g}4,\qquad \sqrt\eta+20C_{\mathrm{pert}}c_y\sqrt{s/\alpha}\le\frac12\sqrt{\eta_w},\qquad C_{\mathrm{pert}}=3,\ c_{\mathrm{pert}}=\tfrac1{100}.
--   $$
--
--   Consider one call of Center with objective $c$ that starts at $y^\circ\in\Omega$ with $\lambda_c(y^\circ)\le1/10$ and with a weight accurate at $y^\circ$, and suppose that its phase preconditioner $P=\alpha\hat Q_0$ satisfies
--   $$
--   \tfrac12P\preceq\nabla^2F(y^\circ)\preceq(4s+2)P. \tag{9.3}
--   $$
--   Suppose also that every query of the call returns estimates with
--   $$
--   \|\hat g-g_G(y)\|_{\nabla^2F(y)^{-1}}\le\varepsilon_g/4,\qquad\|\hat R-R_G(y)\|_F\le\tau \tag{9.10}
--   $$
--   whenever this query and all preceding queries of the call are valid, where $(y,G)$ is its query state. Then:
--
--   1. every query of the call is valid (in particular, no weight update fails);
--   2. every point-update segment lies in the phase ball $B(y^\circ)$ and has F-local length less than $20s\gamma_y$;
--   3. the call returns a feasible point $y$ with $\lambda_c(y)\le\delta_c$;
--   4. at this point, both the final weight and the weight of the last query have gap less than $\eta/2$.
--
--   This is the per-call guarantee of the path-following method of Part II: a y-step taken with an accurate weight leaves a warm weight, and the following G-steps restore accuracy, so the induction over the calls of a run (Theorem 9.7) can proceed.
--
--   **Formalization Note** The oracle is an arbitrary zero-indexed sequence of answers, constrained only by (9.10) and the output types of the estimation data structure at the call's queries; Loewner comparisons are inequalities of quadratic forms; validity also records that a query is reached with a feasible point and a positive definite weight.
--
--   Differences from the source:
--   - encoding: the setting of Part II: 1 ≤ m ≤ n, real symmetric A₁,…,A_m, C with (4.3), F = αΦ_p with s, α of Definition 5.1 (pp.48, 53, 32) → hypotheses hm, hmn, hA, hC, hΩ, hlin, hker; s := sParam m n, α := alphaParam s, F := barrierF A C; reason: the standing assumptions of Part II written as binders; same instances
--   - generalization: c_w, η₀, c_y sufficiently small absolute constants chosen subject to c_w ≤ c_pert/4, η ≤ η_w/16, c_y ≤ 1/200 and (8.12) → any positive reals c_w, η₀, c_y satisfying exactly these printed constraints at the instance’s s; reason: a fixed absolute choice meeting the constraints meets them at every s, so the Lean statement specializes to the paper’s; the proof uses only these constraints
--   - generalization: assume that all queries of the run before this call are valid → hypothesis omitted; reason: it enters the proof only through (9.10), which is stated for the call’s own queries exactly as printed; the Lean theorem holds without it and specializes to the paper’s
--   - encoding: the oracle (BarrierOracle with D_slack, D_weight, D_est) answering one-indexed run queries → an arbitrary zero-indexed answer sequence ans j = (ĝ_j, R̂_j, Q̂_j), with R̂_j symmetric for j < N_c and Q̂₀ ≻ 0 (the output types used from Theorem 8.6); reason: Center is deterministic given its answers, so every adaptive oracle yields some sequence; shifting the call's query indices by one changes no instance; (9.10) is the only accuracy constraint the theorem places on the answers
--   - encoding: the call starts at y° with λ_c(y°) ≤ 1/10 and a weight accurate at y° → y° ∈ Ω, newtonDec ≤ 1/10, G° ≻ 0, weightGap ≤ η; reason: λ_c is defined on Ω and the weight lies in S^m_{++} (Algorithm 5)
--   - encoding: query j valid ((V1)–(V3)) → IsValidQuery: query j reached, y_j ∈ Ω, G_j ≻ 0, and (V1)–(V3); reason: B(y°) ⊆ Ω by Lemma 3.2 and the maintained weight is positive definite, so the extra clauses hold whenever (V1)–(V3) do; they only make the domains explicit
--   - encoding: the call returns a point (implicitly, no UpdateWeight reports failure) → the states of all queries and the final state are some (…), i.e. no update fails; reason: failure of Algorithm 8 is modeled as none and its absence is concluded
--   - encoding: the segment has F-local length less than 20sγ_y → the integrand is interval integrable on [0,1] and segLength < 20sγ_y; reason: guards Lean’s value 0 for a non-integrable integrand; F is C³ on Ω ⊇ B(y°), so the integrand is continuous
--   - encoding: (9.3) ½P ⪯ ∇²F(y°) ⪯ (4s+2)P; norms ‖·‖_{∇²F(y)⁻¹}, ‖·‖_F; log; ⌈·⌉; P⁻¹ → quadratic-form inequalities for every h with ∇²F = iteratedFDeriv ℝ 2 F; DoublyOptBandit.dualLocalNorm; LowRankMEG.frobNorm; Real.log; Nat.ceil; Mathlib matrix inverse; reason: same quantities in Lean’s conventions
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Theorem 9.6, p.65 (parameters Eqs. (8.10)–(8.12), pp.58–59; Definitions 8.1, 8.3, pp.53–56; Algorithms 4, 8, pp.55, 82)

import Mathlib
import Definitions.Def_MatrixLeeSidford_sParam
import Definitions.Def_MatrixLeeSidford_alphaParam
import Definitions.Def_MatrixLeeSidford_barrierF
import Definitions.Def_MatrixLeeSidford_dualRegion
import Definitions.Def_LowRankMEG_frobNorm
import Definitions.Def_DoublyOptBandit_LocalNorm
import Definitions.Def_MatrixLeeSidford_Supplement_weightGap
import Definitions.Def_MatrixLeeSidford_Supplement_statMat
import Definitions.Def_MatrixLeeSidford_Supplement_fixedGrad
import Definitions.Def_MatrixLeeSidford_Supplement_newtonDec
import Definitions.Def_MatrixLeeSidford_Supplement_phaseBall
import Definitions.Def_MatrixLeeSidford_Supplement_segLength
import Definitions.Def_MatrixLeeSidford_Supplement_centerState
import Definitions.Def_MatrixLeeSidford_Supplement_IsValidQuery

open Matrix MeasureTheory

namespace MatrixLeeSidford.Supplement

/-- **Theorem 9.6 (Centering with G-steps)** (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), p.65). Part II setting (pp.48, 53): `1 ≤ m ≤ n`,
symmetric `A₁, …, A_m, C` with (4.3), `F = αΦ_p` with `s = 2⌈log(2mn)⌉`, `α = 10⁶s²`; parameters (8.10)–(8.12)
(pp.58–59) with the absolute constants `c_w, η₀, c_y > 0` subject to the printed constraints. Consider one
call of Center with objective `c` that starts at `y°` with `λ_c(y°) ≤ 1/10` and a weight `G°` accurate at
`y°`, whose phase preconditioner `P = αQ̂₀` satisfies (9.3), `½P ⪯ ∇²F(y°) ⪯ (4s+2)P`, and every query of
which returns estimates with `‖ĝ − g_G(y)‖_{∇²F(y)⁻¹} ≤ ε_g/4`, `‖R̂ − R_G(y)‖_F ≤ τ` (9.10) whenever this query
and all preceding queries of the call are valid, `(y, G)` its query state. Then every query of the call is
valid (in particular no `UpdateWeight` fails), every point-update segment lies in `B(y°)` and has F-local
length less than `20sγ_y`, the call returns a feasible `y` with `λ_c(y) ≤ δ_c`, and at this point both the
final weight and the weight of the last query have gap less than `η/2`.

**Formalization Note** The oracle is an arbitrary answer sequence `ans j = (ĝ_j, R̂_j, Q̂_j)` (see
`centerState`), constrained only by (9.10) and by the types of Theorem 8.6 (`R̂_j` symmetric at each
query; `Q̂₀ ≻ 0`, the only `Q̂` Center uses). The hypothesis "all queries of the run before this call are valid" enters the paper's proof
only through (9.10), which is stated here for the call's own queries exactly as printed, so it is dropped.
`y° ∈ Ω` and `G° ≻ 0` are the domains of `λ_c` and of the weight. Loewner comparisons are quadratic forms
`∀ h`; `∇²F(y)[h,h]` is `iteratedFDeriv ℝ 2 F y (fun _ => h)`; dual and local norms are the published
`DoublyOptBandit` ones; `‖·‖_F` is `LowRankMEG.frobNorm`; `log` is natural and `⌈·⌉` is `Nat.ceil`. The
segment conclusion also asserts integrability of the F-local length integrand. -/
theorem theorem_9_6 {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian)
    (hΩ : (dualRegion A C).Nonempty) (hlin : LinearIndependent ℝ A)
    (hker : ∀ v : Fin n → ℝ, (∀ i, A i *ᵥ v = 0) → v = 0)
    (cw η₀ cy : ℝ) (hcw : 0 < cw) (hη₀ : 0 < η₀) (hcy : 0 < cy)
    (c y₀ : EuclideanSpace ℝ (Fin m)) (G₀ : Matrix (Fin m) (Fin m) ℝ)
    (ans : ℕ → EuclideanSpace ℝ (Fin m) × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin m) ℝ) :
    let s := sParam m n
    let α := alphaParam s
    let F := barrierF A C
    -- (8.10)
    let δc : ℝ := 1 / 100
    let μ : ℝ := 1 / 8
    let e₀ : ℝ := 1 / 1600
    let εg : ℝ := e₀ / Real.sqrt (32 * s)
    let E : ℝ := δc ^ 2 / 16
    let d₀ : ℝ := 0.0054
    -- (8.11)
    let γG : ℝ := 1 / (1000 * s)
    let γy : ℝ := cy / s
    let ηw : ℝ := cw / s
    let η : ℝ := η₀ / (α * s ^ 2)
    let τ : ℝ := Real.sqrt η / 32
    let NG : ℕ := ⌈16 / γG * Real.log (4 * ηw / η)⌉₊
    let Ny : ℕ := ⌈1 / (μ * γy) * Real.log (4 * d₀ / E)⌉₊
    let Nc : ℕ := (NG + 1) * Ny
    -- Theorem 8.5
    let Cpert : ℝ := 3
    let cpert : ℝ := 1 / 100
    -- the call
    let P : Matrix (Fin m) (Fin m) ℝ := α • (ans 0).2.2
    let st := centerState α γy γG NG c y₀ G₀ ans
    let valid := IsValidQuery A C s α γy γG η ηw NG c y₀ G₀ ans
    -- constraints on c_w, η₀, c_y ((8.11)–(8.12))
    cw ≤ cpert / 4 → η ≤ ηw / 16 → cy ≤ 1 / 200 →
    Cpert * Real.sqrt (α * s * η) ≤ εg / 4 →
    Real.sqrt η + 20 * Cpert * cy * Real.sqrt (s / α) ≤ 1 / 2 * Real.sqrt ηw →
    -- start of the call
    y₀ ∈ dualRegion A C → newtonDec A C c y₀ ≤ 1 / 10 →
    G₀.PosDef → weightGap A C s y₀ G₀ ≤ η →
    -- answer types (Theorem 8.6)
    (ans 0).2.2.PosDef → (∀ j < Nc, ((ans j).2.1).IsHermitian) →
    -- (9.3)
    (∀ h : EuclideanSpace ℝ (Fin m),
      1 / 2 * (WithLp.ofLp h ⬝ᵥ (P *ᵥ WithLp.ofLp h)) ≤ iteratedFDeriv ℝ 2 F y₀ (fun _ => h) ∧
      iteratedFDeriv ℝ 2 F y₀ (fun _ => h) ≤ (4 * s + 2) * (WithLp.ofLp h ⬝ᵥ (P *ᵥ WithLp.ofLp h))) →
    -- (9.10)
    (∀ j < Nc, ∀ y G, st j = some (y, G) → (∀ i ≤ j, valid i) →
      DoublyOptBandit.dualLocalNorm F y ((ans j).1 - fixedGrad A C s y G) ≤ εg / 4 ∧
      LowRankMEG.frobNorm ((ans j).2.1 - statMat A C s y G) ≤ τ) →
    -- every query of the call is valid
    (∀ j < Nc, valid j) ∧
    -- every point-update segment lies in B(y°) and has F-local length < 20 s γ_y
    (∀ j < Nc, j % (NG + 1) = 0 → ∃ y y' : EuclideanSpace ℝ (Fin m), ∃ G : Matrix (Fin m) (Fin m) ℝ,
      st j = some (y, G) ∧ st (j + 1) = some (y', G) ∧
      (∀ u ∈ Set.Icc (0 : ℝ) 1, y + u • (y' - y) ∈ phaseBall A C y₀) ∧
      IntervalIntegrable
        (fun u : ℝ => DoublyOptBandit.localNorm F (y + u • (y' - y)) (y' - y)) volume 0 1 ∧
      segLength A C y y' < 20 * s * γy) ∧
    -- the returned point, the final weight and the weight of the last query
    (∃ y : EuclideanSpace ℝ (Fin m), ∃ Gf Gl : Matrix (Fin m) (Fin m) ℝ,
      st Nc = some (y, Gf) ∧ st (Nc - 1) = some (y, Gl) ∧
      y ∈ dualRegion A C ∧ newtonDec A C c y ≤ δc ∧
      weightGap A C s y Gf < η / 2 ∧ weightGap A C s y Gl < η / 2) := by sorry

end MatrixLeeSidford.Supplement
