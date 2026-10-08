-- Prove2me | Theorems.Thm_MinimaxSLP_RhsExtremal_theorem_3_3
-- name    : MinimaxSLP.RhsExtremal.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:10.347289+00:00
-- url     : https://prove2.me/theorems/6343b971-7bab-4e42-abbe-c6680e6c319f
-- title:
--   Theorem 3.3, p. 590 — with random right-hand side and known dual extreme points, a distribution in 𝒫 attains Ẑ(x) = Ẑ_DD(x)
-- statement:
--   Consider the two-stage minimax stochastic linear program with random right-hand side $\tilde h\in\mathbb R^r$ and constant objective $q\in\mathbb R^d$, with second-stage cost $\mathcal Q(h,x)=\max\{(h-Tx)'p : W'p\le q\}$, disutility $\mathbb U(t)=\max_{k}(\alpha_k t+\beta_k)$ with $\alpha_k\ge0$, and moment class $\mathcal P=\{P : \mathbb E_P[\tilde h]=\mu,\ \mathbb E_P[\tilde h\tilde h']=Q\}$. Assume
--
--   1. complete recourse: $\{Ww : w\ge 0\}=\mathbb R^r$ (Assumption 2);
--   2. $\{p\in\mathbb R^r : W'p\le q\}\neq\emptyset$ (Assumption 3 at the constant $q$);
--   3. $Q$ is symmetric and $Q\succ\mu\mu'$ (Assumption 4);
--   4. $p_1,\dots,p_N$ are the extreme points of $\{p : W'p\le q\}$ (Assumption 5).
--
--   **Theorem 3.3.** For an arbitrary $x\in X$, there exists an extremal distribution in $\mathcal P$ that achieves the optimal value $\hat Z(x)$. Precisely, there is $P\in\mathcal P$ such that $\mathbb U(\mathcal Q(\cdot,x))$ is integrable under every $P'\in\mathcal P$ and
--   $$
--   \mathbb E_{P'}\big[\mathbb U(\mathcal Q(\tilde h,x))\big]\le\mathbb E_{P}\big[\mathbb U(\mathcal Q(\tilde h,x))\big]\quad\forall P'\in\mathcal P,
--   $$
--   the value $\mathbb E_{P}[\mathbb U(\mathcal Q(\tilde h,x))]$ is the attained maximum of (16), and
--   $$
--   \mathbb E_{P}\big[\mathbb U(\mathcal Q(\tilde h,x))\big]=\hat Z(x)=\hat Z_{DD}(x).
--   $$
--
--   The worst-case distribution is therefore a genuine member of the moment class, not only a limit, and it can be written down from an optimal solution of the semidefinite program (16) as a finite mixture of normal distributions.
--
--   **Formalization Note** As printed, Assumption 2 and Assumption 3 "for all $q$" contradict each other when $r\ge1$; the §3 reading uses complete recourse and dual feasibility at the one constant $q$. Assumption 1 ($X$ bounded and nonempty) is not used and is omitted; $x\in X$ is kept as printed. No strong-duality hypothesis is made: the proof does not need one. The maximality over $\mathcal P$ is stated directly, so the claim does not depend on junk values of `sSup`.
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, p. 590, Theorem 3.3 (proof pp. 590–591)

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_RhsExtremal_Model

namespace MinimaxSLP.RhsExtremal

open MeasureTheory Matrix

/-- Theorem 3.3, p. 590. Under Assumptions 2 (complete recourse), 3 (at the constant `q`),
4 and 5, and `α_k ≥ 0`, for an arbitrary `x ∈ MinimaxSLP.ObjSDP.X` there is a distribution `P ∈ 𝒫` that attains
the optimal value `Ẑ(x)`: `𝕌(𝒬(·, x))` is integrable under every `P′ ∈ 𝒫` and
`E_{P′}[𝕌(𝒬(h̃, x))] ≤ E_P[𝕌(𝒬(h̃, x))]`; moreover `E_P[𝕌(𝒬(h̃, x))]` is the attained maximum
of (16), and `E_P[𝕌(𝒬(h̃, x))] = Ẑ(x) = Ẑ_DD(x)`. -/
theorem theorem_3_3 {m₁ n r d K N : ℕ} [NeZero K]
    (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ)
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (q : Fin d → ℝ)
    (α β : Fin K → ℝ) (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ)
    (ps : Fin N → Fin r → ℝ)
    (hα : ∀ k, 0 ≤ α k)
    (hA2 : ∀ z : Fin r → ℝ, ∃ w : Fin d → ℝ, 0 ≤ w ∧ W *ᵥ w = z)
    (hA3 : ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (hQ : Q.IsSymm) (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef)
    (hA5 : Set.range ps = Set.extremePoints ℝ {π : Fin r → ℝ | Wᵀ *ᵥ π ≤ q})
    (x : Fin n → ℝ) (hx : x ∈ MinimaxSLP.ObjSDP.X A b) :
    ∃ P ∈ MinimaxSLP.ObjSDP.momentClass μ Q,
      (∀ P' ∈ MinimaxSLP.ObjSDP.momentClass μ Q,
        Integrable (fun h => MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x)) P' ∧
        ∫ h, MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x) ∂P' ≤ ∫ h, MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x) ∂P) ∧
      IsGreatest (obj16 T α β ps x '' feasible16 K N μ Q)
        (∫ h, MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x) ∂P) ∧
      MinimaxSLP.RhsSDP.Zhat W T q α β μ Q x = ∫ h, MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x) ∂P ∧
      ZhatDD T α β ps μ Q x = ∫ h, MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x) ∂P := by sorry

end MinimaxSLP.RhsExtremal
