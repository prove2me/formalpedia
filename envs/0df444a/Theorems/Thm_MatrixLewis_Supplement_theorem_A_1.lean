-- Prove2me | Theorems.Thm_MatrixLewis_Supplement_theorem_A_1
-- name    : MatrixLewis.Supplement.theorem_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:09:36.363511+00:00
-- url     : https://prove2.me/theorems/03c24516-a72c-458b-9100-aba1e08bb867
-- title:
--   Theorem A.1 — two-phase initialization: $Q_{\mathrm{run}}$ queries, output with $\lambda_c(x,\mu_f)\le\bar\lambda/4$ and $c^\top x-\mathrm{opt}\le2\mu_fm$
-- statement:
--   Keep the conventions of Section 4.1: Assumption 3.1, a real $q>2$, $m\ge1$, a self-concordance constant $K\ge1$ of $f_q$ (that is, $|D^3f_q(x)[h,h,h]|\le2K(D^2f_q(x)[h,h])^{3/2}$ on $\mathcal D$), and $\kappa\ge1$. There are absolute constants $c_0,c_e\in(0,1/4]$, $C_{\mathrm{blk}}\ge1$ and $C$ such that the following holds.
--
--   Let the instance be bounded: $\mathcal D$ is nonempty and bounded, with size bounds $R_{\mathcal D}=\sup_{x\in\mathcal D}\|x\|_\infty$ and $R_S=\sup_{x\in\mathcal D}\|S_x\|_{\mathrm{op}}$. Let $x_0\in\mathcal D$ with $S_{x_0}\succeq\rho I$ for some $\rho>0$, let $\bar a\ge\max\{1,R_S/\rho\}$ and $\bar R_{\mathcal D}\ge R_{\mathcal D}$, let $c\in\mathbb R^m\setminus\{0\}$ and $\mu_f>0$. Run Algorithm 4 with $K$, $\kappa$ and the parameters of Theorem 4.5, and call an answer good if it is $(\kappa,e_{\mathrm{PA}})$-good. Let $P_{\mathrm I}$ and $P_{\mathrm{II}}$ be the numbers $P$ of its two runs of PF.
--
--   The algorithm makes $Q_{\mathrm{run}}:=1+(P_{\mathrm I}+P_{\mathrm{II}}+2)\tau_{\mathrm{blk}}$ queries unless it halts with FAIL, and
--   $$Q_{\mathrm{run}}\le C\Bigl(1+K\sqrt m\bigl(\log\mu_{\mathrm{top}}+|\log(\mu_1/\mu_f)|\bigr)\Bigr)(q+1)\kappa^2 .$$
--
--   1. If all answers before a query are good, then the point of that query lies in $\mathcal D$.
--   2. If all answers are good, then the output $x$ lies in $\mathcal D$ and satisfies $\lambda_c(x,\mu_f)\le\bar\lambda/4$ and
--   $$c^\top x-\mathrm{opt}\le2\mu_fm,\qquad \mathrm{opt}:=\inf\{c^\top y:S_y\succeq0\},$$
--   where $\mathrm{opt}$ is finite.
--   3. With a $(\kappa,e_{\mathrm{PA}},p_{\mathrm{ans}})$-oracle ($0\le p_{\mathrm{ans}}<1$), all answers are good with probability at least $1-Q_{\mathrm{run}}p_{\mathrm{ans}}$.
--
--   This theorem lets path following start from any strictly feasible point with known bounds, at the price of only logarithmic factors in those bounds. It is the initialization behind the paper's complexity bound on general instances.
--
--   **Formalization Note** The finiteness of $\mathrm{opt}$ is stated as a conclusion: the set $\{c^\top y:S_y\succeq0\}$ is nonempty and bounded below, and $\mathrm{opt}$ is its real infimum. Parts 1 and 2 hold for every answerer. Part 3 bounds $\mu(\text{some answer is not good})$ for the random run of an oracle. Queries are numbered from $0$, the query at $x_0$.
--
--   Differences from the source:
--   - encoding: absolute constants of Lemma 4.4 (the parameters of Theorem 4.5) and O(·) → ∃ c₀, c_e ∈ (0, 1/4], C_blk ≥ 1 and one C₀ > 0, quantified before all data; reason: O(·) hides an absolute constant; Lemma 4.4 states the ranges
--   - encoding: "unless it halts with FAIL", "all answers good" for the adaptive, deterministic-given-answers method → the run as a function of an answerer R : ℕ → Query → Answer; (a), (b) for every R; queries indexed from 0; reason: the method is deterministic given the answers (p.63) and every answer stream is the run of some R
--   - encoding: probability at least 1 − Q_run p_ans that all answers are good → μ{ω : some answer is not good} ≤ Q_run p_ans for the run of an oracle (IsOracle); reason: complement form of the same bound, not weaker
--   - encoding: opt := inf{c⊤y : S_y ⪰ 0} is finite → the image set is nonempty and BddBelow, and opt is its real sInf; reason: makes "finite" a conclusion and excludes the junk value of sInf
--   - encoding: R_𝒟 = sup ‖x‖_∞, R_S = sup ‖S_x‖_op on a bounded instance → real sSup over 𝒟, with 𝒟 bounded as a hypothesis and nonempty through x₀ ∈ 𝒟; reason: the suprema are the paper's values under exactly these hypotheses
--   - encoding: bounded instance (Assumption 3.1, 𝒟 nonempty and bounded) → Assumption31 A and Bornology.IsBounded 𝒟, with no separate nonemptiness binder; reason: x₀ ∈ 𝒟 already gives 𝒟 ≠ ∅
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Theorem A.1, p.62 (proof pp.62–63); Algorithm 4, p.62; conventions of §4.1 kept, p.61

import Mathlib
import Definitions.Def_MatrixLewis_Assumption31
import Definitions.Def_MatrixLewis_Supplement_TwoPhase

open MeasureTheory

namespace MatrixLewis

namespace Supplement

/-- **Theorem A.1** (Two-phase initialization; Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights:
Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission
(manuscript sha256 31ce765b…), p.62). Run Algorithm 4 with `K`, `κ` and the parameters of Theorem 4.5,
and call an answer good if it is `(κ, e_PA)`-good. Let `P_I` and `P_II` be the numbers `P` of its two
runs of `PF`. It makes `Q_run := 1 + (P_I + P_II + 2)τ_blk` queries unless it halts with `FAIL`, and
`Q_run = O((1 + K√m (log μ_top + |log(μ₁/μ_f)|))(q + 1)κ²)`.
(a) If all answers before a query are good, then the point of that query lies in `𝒟`.
(b) If all answers are good, then the output `x` lies in `𝒟` and satisfies `λ_c(x, μ_f) ≤ λ̄/4` and
`c⊤x − opt ≤ 2μ_f m`, where `opt := inf{c⊤y : S_y ⪰ 0}` is finite.
(c) With a `(κ, e_PA, p_ans)`-oracle, all answers are good with probability at least `1 − Q_run p_ans`.

Algorithm 4 requires a bounded instance (Assumption 3.1, `𝒟` nonempty and bounded) with size bounds
`R_𝒟 = sup_{x∈𝒟} ‖x‖_∞` and `R_S = sup_{x∈𝒟} ‖S_x‖_op`, a point `x₀ ∈ 𝒟` with `S_{x₀} ⪰ ρI` for some
`ρ > 0`, numbers `ā ≥ max{1, R_S/ρ}` and `R̄_𝒟 ≥ R_𝒟`, an objective `c ∈ ℝᵐ \ {0}`, and `μ_f > 0`.

**Formalization Note** The conventions of §4.1 are kept (App. A, p.61): `q > 2` real, `m ≥ 1`,
symmetric data, a self-concordance constant `K ≥ 1` (`|D³f_q[h,h,h]| ≤ 2K(D²f_q[h,h])^{3/2}` on `𝒟`),
`κ ≥ 1`. A bounded instance is Assumption 3.1 with `𝒟` bounded; nonemptiness of `𝒟` is implied by
`x₀ ∈ 𝒟`. The constants `c₀, c_e ∈ (0, 1/4]`, `C_blk ≥ 1` of Lemma 4.4 and the constant `C` of the `O` are
quantified first. Parts (a) and (b) hold for every answerer `R` (every answer stream); part (c) is for
the random run of an oracle (`IsOracle`), as `μ(some answer is not good) ≤ Q_run p_ans`. "`opt` is
finite" is the conclusion that `{c⊤y : S_y ⪰ 0}` is nonempty and bounded below; `opt` is its real
infimum. `log` is natural. -/
theorem theorem_A_1 :
    ∃ c0 ce Cblk : ℝ, 0 < c0 ∧ c0 ≤ 1 / 4 ∧ 0 < ce ∧ ce ≤ 1 / 4 ∧ 1 ≤ Cblk ∧
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ (n m : ℕ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
          (q K κ : ℝ),
        1 ≤ m → (∀ i, (A i).IsHermitian) → C.IsHermitian → Assumption31 A → 2 < q →
        1 ≤ K →
        (∀ x ∈ dom A C, ∀ h : EuclideanSpace ℝ (Fin m),
          |iteratedFDeriv ℝ 3 (barrier q A C) x (fun _ => h)| ≤
            2 * K * (iteratedFDeriv ℝ 2 (barrier q A C) x (fun _ => h)) ^ ((3 : ℝ) / 2)) →
        1 ≤ κ →
        -- a bounded instance (𝒟 is nonempty as `x0 ∈ 𝒟`)
        Bornology.IsBounded (dom A C) →
        ∀ (x0 : EuclideanSpace ℝ (Fin m)) (ρ abar Rbar : ℝ) (c : EuclideanSpace ℝ (Fin m)) (μf : ℝ),
          x0 ∈ dom A C → 0 < ρ → (slack A C x0 - ρ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef →
          max 1 (sizeBoundS A C / ρ) ≤ abar → sizeBoundD A C ≤ Rbar → c ≠ 0 → 0 < μf →
          let pr : PFParams := ⟨c0, ce, Cblk, q, K, κ, m⟩
          let PI : ℕ := pr.numP 1 (muTop pr abar)
          let PII : ℕ := pr.numP (muOne pr Rbar c) μf
          let Qrun : ℕ := 1 + (PI + PII + 2) * pr.tauBlk
          let good : Query m → Answer m → Prop := IsGood q A C κ pr.ePA
          let opt : ℝ := sInf ((fun y : EuclideanSpace ℝ (Fin m) => ∑ i, c i * y i) ''
            {y | (slack A C y).PosSemidef})
          -- the query count
          (∀ R : ℕ → Query m → Answer m, twoPhaseOutput pr x0 abar Rbar c μf R ≠ none →
            ∀ t, (twoPhaseQuery pr x0 abar Rbar c μf R t).isSome ↔ t < Qrun) ∧
          (Qrun : ℝ) ≤ C0 * ((1 + K * Real.sqrt m * (Real.log (muTop pr abar) +
              |Real.log (muOne pr Rbar c / μf)|)) * (q + 1) * κ ^ 2) ∧
          -- (a)
          (∀ (R : ℕ → Query m → Answer m) (t : ℕ) (Qt : Query m),
            twoPhaseQuery pr x0 abar Rbar c μf R t = some Qt →
            (∀ s < t, ∀ Qs, twoPhaseQuery pr x0 abar Rbar c μf R s = some Qs →
              good Qs (R s Qs)) →
            Qt.1 ∈ dom A C) ∧
          -- (b)
          (∀ R : ℕ → Query m → Answer m,
            (∀ t Qt, twoPhaseQuery pr x0 abar Rbar c μf R t = some Qt → good Qt (R t Qt)) →
            ∃ y, twoPhaseOutput pr x0 abar Rbar c μf R = some y ∧ y ∈ dom A C ∧
              newtonDec q A C c y μf ≤ pr.lamBar / 4 ∧
              ((fun z : EuclideanSpace ℝ (Fin m) => ∑ i, c i * z i) ''
                {z | (slack A C z).PosSemidef}).Nonempty ∧
              BddBelow ((fun z : EuclideanSpace ℝ (Fin m) => ∑ i, c i * z i) ''
                {z | (slack A C z).PosSemidef}) ∧
              ∑ i, c i * y i - opt ≤ 2 * μf * m) ∧
          -- (c)
          (∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
              (ℱ : Filtration ℕ mΩ) (O : ℕ → Ω → Query m → Answer m) (pans : ℝ),
            0 ≤ pans → pans < 1 → IsOracle q A C κ pr.ePA pans μ ℱ O →
            μ {ω | ¬ ∀ t Qt, twoPhaseQuery pr x0 abar Rbar c μf (fun u => O u ω) t = some Qt →
                good Qt (O t ω Qt)} ≤ ENNReal.ofReal (Qrun * pans)) := by sorry

end Supplement

end MatrixLewis
