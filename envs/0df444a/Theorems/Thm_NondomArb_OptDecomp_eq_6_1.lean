-- Prove2me | Theorems.Thm_NondomArb_OptDecomp_eq_6_1
-- name    : NondomArb.OptDecomp.eq_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:19:06.720986+00:00
-- url     : https://prove2.me/theorems/be1d0565-bfeb-48d3-a036-bd9a92ca52d7
-- title:
--   (6.1), proof of Theorem 6.1, p. 34 — ℰ_t(V_{t+1}) ≤ V_t 𝒫-q.s. for a supermartingale under every Q ∈ 𝒬
-- statement:
--   Consider the nondominated market of §1.2 without options ($e = 0$), let NA($\mathcal P$) hold, and let $V$ be an adapted real-valued process such that $V_t$ is upper semianalytic and in $L^1(Q)$ for all $Q \in \mathcal Q$ and $t \in \{1, 2, \dots, T\}$. Assume moreover that $V$ is a supermartingale under each $Q \in \mathcal Q$ (condition (i) of Theorem 6.1).
--
--   **Claim (6.1).** For every $t \in \{0, 1, \dots, T-1\}$,
--   $$\mathcal E_t(V_{t+1}) \le V_t \quad \mathcal P\text{-q.s.}, \tag{6.1}$$
--   where $V_{t+1}$ is regarded as a function on $\Omega_t \times \Omega_1$ and $\mathcal E_t(V_{t+1})(\omega) = \sup_{Q \in \mathcal Q_t(\omega)} E_Q[V_{t+1}(\omega, \cdot)]$ is the conditional sublinear expectation of Lemma 4.10.
--
--   The claim converts the supermartingale property under every martingale measure into a one-step inequality for the worst-case conditional expectation. Combined with the measurable one-step hedge of Lemma 4.10 it yields the decomposition of Theorem 6.1.
--
--   **Formalization Note.** The inequality is in $[-\infty, \infty]$ (`EReal`), and "$\mathcal P$-q.s." is read on $\Omega$ through the prefix map $\omega \mapsto (\omega_1, \dots, \omega_t)$.
-- source:
--   Bouchard, Nutz, Arbitrage and duality in nondominated discrete-time models, arXiv:1305.6008v3, p. 34, §6, proof of Theorem 6.1, (6.1)

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability
import Definitions.Def_NondomArb_OptDecomp_Model
import Definitions.Def_NondomArb_OptDecomp_Process

open MeasureTheory BertsekasShreve.AnalyticSelection

namespace NondomArb.OptDecomp

/-- **(6.1)**, proof of Theorem 6.1 (Bouchard–Nutz, p. 34). In the market of §1.2 without
options (`e = 0`), let `NA(𝒫)` hold and let `V` be an adapted process such that `V_t` is
upper semianalytic and in `L¹(Q)` for all `Q ∈ 𝒬` and `t ∈ {1, …, T}`, and such that `V` is a
supermartingale under each `Q ∈ 𝒬`. Then for every `t ∈ {0, …, T − 1}`,
`ℰ_t(V_{t+1}) ≤ V_t` `𝒫`-q.s., where `V_{t+1}` is read on `Ω_t × Ω₁` and
`ℰ_t(V_{t+1})(ω) = sup_{Q ∈ 𝒬_t(ω)} E_Q[V_{t+1}(ω, ·)]`. -/
theorem eq_6_1 {Ω₁ : Type*} [TopologicalSpace Ω₁] [PolishSpace Ω₁] [MeasurableSpace Ω₁]
    [BorelSpace Ω₁] {T d : ℕ} (M : Market Ω₁ T d 0) (hM : M.Standing) (hNA : M.NA)
    (V : (t : ℕ) → (Fin t → Ω₁) → ℝ) (hV : M.Adapted V)
    (hVusa : ∀ t, 1 ≤ t → t ≤ T → NondomArb.Superhedge.IsUpperSemianalytic (fun ω : Fin t → Ω₁ => ((V t ω : ℝ) : EReal)))
    (hVint : ∀ Q ∈ M.MartMeasures, ∀ t (ht1 : 1 ≤ t) (ht : t ≤ T),
      Integrable (fun ω => V t (NondomArb.Superhedge.pre ω t ht)) Q)
    (hsuper : ∀ Q ∈ M.MartMeasures, M.IsSupermartingale V Q)
    (t : ℕ) (ht : t < T) :
    M.QS (fun ω =>
      M.condSup t (fun p => ((V (t + 1) (Fin.snoc (α := fun _ => Ω₁) p.1 p.2) : ℝ) : EReal))
        (NondomArb.Superhedge.pre ω t ht.le) ≤ ((V t (NondomArb.Superhedge.pre ω t ht.le) : ℝ) : EReal)) := by sorry

end NondomArb.OptDecomp
