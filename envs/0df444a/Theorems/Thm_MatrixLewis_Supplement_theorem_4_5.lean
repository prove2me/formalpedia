-- Prove2me | Theorems.Thm_MatrixLewis_Supplement_theorem_4_5
-- name    : MatrixLewis.Supplement.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:08:32.723872+00:00
-- url     : https://prove2.me/theorems/2778a043-b5b8-41c6-b060-23f1aec2e2fd
-- title:
--   Theorem 4.5 — path following with approximate answers: $(P+1)\tau_{\mathrm{blk}}=O((1+K\sqrt m|\log(\mu_e/\mu_s)|)(q+1)\kappa^2)$ queries, all good w.p. $\ge1-(P+1)\tau_{\mathrm{blk}}p_{\mathrm{ans}}$
-- statement:
--   Assume Assumption 3.1, let $q>2$ be real and $m\ge1$, let $K\ge1$ be a self-concordance constant of $f_q$, i.e. $|D^3f_q(x)[h,h,h]|\le2K(D^2f_q(x)[h,h])^{3/2}$ for all $x\in\mathcal D$, $h\in\mathbb R^m$, and fix $\kappa\ge1$. There are absolute constants $c_0,c_e\in(0,1/4]$ and $C_{\mathrm{blk}}\ge1$ (those of Lemma 4.4), and an absolute constant $C$, such that the following holds for Algorithm 2 with the parameters of Equation (47), calling an answer good if it is $(\kappa,e_{\mathrm{PA}})$-good.
--
--   Let $c'\in\mathbb R^m$, $\mu_s,\mu_e>0$ and $x\in\mathcal D$ with $\lambda_{c'}(x,\mu_s)\le\bar\lambda$. Then $\mathrm{PF}(c',x,\mu_s\to\mu_e)$ makes $(P+1)\tau_{\mathrm{blk}}$ queries unless it halts with FAIL, and
--   $$(P+1)\tau_{\mathrm{blk}}\le C\bigl(1+K\sqrt m\,|\log(\mu_e/\mu_s)|\bigr)(q+1)\kappa^2 .$$
--
--   1. If all answers before a query are good, then the point of that query lies in $\mathcal D$.
--   2. If all answers are good, then the output $x$ lies in $\mathcal D$ and satisfies $\lambda_{c'}(x,\mu_e)\le\bar\lambda/4$. Moreover, $c'^\top x\le c'^\top y+2\mu_em$ for every $y\in\mathbb R^m$ with $S_y\succeq0$.
--   3. With a $(\kappa,e_{\mathrm{PA}},p_{\mathrm{ans}})$-oracle ($0\le p_{\mathrm{ans}}<1$), all answers are good with probability at least $1-(P+1)\tau_{\mathrm{blk}}p_{\mathrm{ans}}$.
--
--   In particular, at $q\ge\log n$ with $K=K_q$ and $\kappa=O(1)$, the method makes $O(q^2\sqrt m)$ queries per constant-factor change of $\mu$, with $e_{\mathrm{PA}}=\Theta(q^{-3/2})$, and likewise at $q=\Theta(\log n)$ with $K=K_{q,n}=O(q)$. Precisely: for every $C'>0$, $\kappa_0\ge1$ and $\Gamma>1$ there are $C_1,c_1>0$ such that, whenever $q\ge\log n$, $K=C'q$, $1\le\kappa\le\kappa_0$ and $\Gamma^{-1}\le\mu_e/\mu_s\le\Gamma$,
--   $$(P+1)\tau_{\mathrm{blk}}\le C_1q^2\sqrt m,\qquad c_1q^{-3/2}\le e_{\mathrm{PA}}\le C_1q^{-3/2},$$
--   and the same holds, for every $C_{\mathrm{sc}}\ge1$ and $0<c_1'\le c_2'$, with $K=C_{\mathrm{sc}}q(1+\sqrt{2n^{2/(q+2)}})$ and $c_1'\log n\le q\le c_2'\log n$ in place of $q\ge\log n$ and $K=C'q$.
--
--   This is the paper's guarantee for short-step path following with approximate, possibly failing answers. With the self-concordance of Section 3 it gives the iteration count of the paper's main result.
--
--   **Formalization Note** Parts 1 and 2 hold for every way of answering the queries (every answerer). Part 3 is stated as $\mu(\text{some answer is not good})\le(P+1)\tau_{\mathrm{blk}}p_{\mathrm{ans}}$ for the random run of an oracle in the sense of Definition 4.1. The count is stated exactly: if the run does not halt, its queries are exactly those numbered $0,\dots,(P+1)\tau_{\mathrm{blk}}-1$. The "in particular" bounds are arithmetic in the parameters.
--
--   Differences from the source:
--   - encoding: absolute constants c₀, c_e, C_blk fixed in the proof of Lemma 4.4, and O(·) → ∃ c₀, c_e ∈ (0, 1/4], C_blk ≥ 1 and one C₀ > 0, quantified before all data; reason: O(·) hides an absolute constant; Lemma 4.4 states the ranges
--   - encoding: "unless it halts with FAIL", "all answers good" for the adaptive, deterministic-given-answers method → the run as a function of an answerer R : ℕ → Query → Answer; (a), (b) for every R; queries indexed from 0; reason: the method is deterministic given the answers (p.40) and every answer stream is the run of some R
--   - encoding: probability at least 1 − (P + 1)τ_blk p_ans that all answers are good → μ{ω : some answer is not good} ≤ (P + 1)τ_blk p_ans, for the run R = O(·, ω) of an oracle (IsOracle, Definition 4.1); reason: complement form of the same bound; for a measurable event the two agree, and the outer-measure bound is not weaker
--   - reading: q ≥ log n, K = K_q, κ = O(1), per constant-factor change of µ, e_PA = Θ(q^{−3/2}), and q = Θ(log n) with K = K_{q,n} → ∀ C′ > 0, κ₀ ≥ 1, Γ > 1 ∃ C₁, c₁ > 0 for K = C′q, 1 ≤ κ ≤ κ₀, Γ⁻¹ ≤ µ_e/µ_s ≤ Γ; and ∀ C_sc ≥ 1, 0 < c₁ ≤ c₂ the same for K = C_sc q(1 + √(2n^{2/(q+2)})), c₁ log n ≤ q ≤ c₂ log n; reason: the standard meaning of O and Θ, with the constants depending on the fixed parameters; same Θ(log n) reading as the published goal
--   - generalization: the "in particular" clause for K = K_q with Corollary 3.22's constant C′_sc and for instances of the program → every C′ > 0 and all natural n, m ≥ 1 and real q, without data; reason: the clause concerns only the parameter values (P + 1)τ_blk and e_PA, so the paper's instances and C′_sc are among those covered
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Theorem 4.5, p.39 (proof pp.39–40); Equation (47) and Algorithm 2, p.37; standing assumptions of §4.1, p.35

import Mathlib
import Definitions.Def_MatrixLewis_Assumption31
import Definitions.Def_MatrixLewis_Supplement_PathFollowing

open MeasureTheory

namespace MatrixLewis

namespace Supplement

/-- **Theorem 4.5** (Path following with approximate answers; Kelner–Jiang–Sidford–Zhang, *Matrix
Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027
submission (manuscript sha256 31ce765b…), p.39). Take Algorithm 2 with the parameters of
Equation (47), and call an answer good if it is `(κ, e_PA)`-good. Let `c′ ∈ ℝᵐ`, `μ_s, μ_e > 0`, and
`x ∈ 𝒟` with `λ_{c′}(x, μ_s) ≤ λ̄`. Then `PF(c′, x, μ_s → μ_e)` makes `(P + 1)τ_blk` queries unless it
halts with `FAIL`, and `(P + 1)τ_blk = O((1 + K√m |log(μ_e/μ_s)|)(q + 1)κ²)`.
(a) If all answers before a query are good, then the point of that query lies in `𝒟`.
(b) If all answers are good, then the output `x` lies in `𝒟` and satisfies `λ_{c′}(x, μ_e) ≤ λ̄/4`.
Moreover, `c′⊤x ≤ c′⊤y + 2μ_e m` for every `y ∈ ℝᵐ` with `S_y ⪰ 0`.
(c) With a `(κ, e_PA, p_ans)`-oracle, all answers are good with probability at least
`1 − (P + 1)τ_blk p_ans`.
In particular, at `q ≥ log n` with `K = K_q` and `κ = O(1)`, the method makes `O(q²√m)` queries per
constant-factor change of `μ`, with `e_PA = Θ(q^{−3/2})`, and likewise at `q = Θ(log n)` with
`K = K_{q,n} = O(q)` (Theorem 3.21).

**Formalization Note** Standing assumptions of §4.1 (p.35): `q > 2` real, Assumption 3.1, `m ≥ 1`,
symmetric data, and a self-concordance constant `K ≥ 1`: `|D³f_q(x)[h,h,h]| ≤ 2K(D²f_q(x)[h,h])^{3/2}`
on `𝒟`; `κ ≥ 1`. The constants `c₀, c_e ∈ (0, 1/4]`, `C_blk ≥ 1` of Lemma 4.4 (fixed in its proof) and
the constant `C` of every `O`/`Θ` are quantified first. The `O` of the count is one absolute constant.
Parts (a) and (b) hold for every answerer `R` (every answer stream); part (c) is for the random run
`R = O · ω` of an oracle (`IsOracle`, Definition 4.1), as the bound `μ(some answer is not good) ≤
(P + 1)τ_blk p_ans`. "All answers good" ranges over the queries the run makes. The "in particular"
clause is arithmetic in the parameters (it holds without data): `K = K_q` is read as `K = C′q` for every
`C′ > 0` (Corollary 3.22's `C′_sc` among them), `K = K_{q,n}` as `K = C_sc q(1 + √(2n^{2/(q+2)}))` for
every `C_sc ≥ 1`, `κ = O(1)` as `1 ≤ κ ≤ κ₀`, "per constant-factor change of `μ`" as
`Γ⁻¹ ≤ μ_e/μ_s ≤ Γ`, and `q = Θ(log n)` as `c₁ log n ≤ q ≤ c₂ log n`; the constants depend on
`C′`/`C_sc`, `κ₀`, `Γ` and `c₁, c₂` only. `log` is natural. -/
theorem theorem_4_5 :
    ∃ c0 ce Cblk : ℝ, 0 < c0 ∧ c0 ≤ 1 / 4 ∧ 0 < ce ∧ ce ≤ 1 / 4 ∧ 1 ≤ Cblk ∧
    ∃ C0 : ℝ, 0 < C0 ∧
      (∀ (n m : ℕ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
          (q K κ : ℝ),
        1 ≤ m → (∀ i, (A i).IsHermitian) → C.IsHermitian → Assumption31 A → 2 < q →
        1 ≤ K →
        (∀ x ∈ dom A C, ∀ h : EuclideanSpace ℝ (Fin m),
          |iteratedFDeriv ℝ 3 (barrier q A C) x (fun _ => h)| ≤
            2 * K * (iteratedFDeriv ℝ 2 (barrier q A C) x (fun _ => h)) ^ ((3 : ℝ) / 2)) →
        1 ≤ κ →
        let pr : PFParams := ⟨c0, ce, Cblk, q, K, κ, m⟩
        ∀ (c' : EuclideanSpace ℝ (Fin m)) (μs μe : ℝ) (x : EuclideanSpace ℝ (Fin m)),
          0 < μs → 0 < μe → x ∈ dom A C → newtonDec q A C c' x μs ≤ pr.lamBar →
          let NQ : ℕ := (pr.numP μs μe + 1) * pr.tauBlk
          let good : Query m → Answer m → Prop := IsGood q A C κ pr.ePA
          -- the query count
          (∀ R : ℕ → Query m → Answer m, pfOutput pr c' x μs μe R ≠ none →
            ∀ t, (pfQuery pr c' x μs μe R t).isSome ↔ t < NQ) ∧
          (NQ : ℝ) ≤
            C0 * ((1 + K * Real.sqrt m * |Real.log (μe / μs)|) * (q + 1) * κ ^ 2) ∧
          -- (a)
          (∀ (R : ℕ → Query m → Answer m) (t : ℕ) (Qt : Query m),
            pfQuery pr c' x μs μe R t = some Qt →
            (∀ s < t, ∀ Qs, pfQuery pr c' x μs μe R s = some Qs → good Qs (R s Qs)) →
            Qt.1 ∈ dom A C) ∧
          -- (b)
          (∀ R : ℕ → Query m → Answer m,
            (∀ t Qt, pfQuery pr c' x μs μe R t = some Qt → good Qt (R t Qt)) →
            ∃ y, pfOutput pr c' x μs μe R = some y ∧ y ∈ dom A C ∧
              newtonDec q A C c' y μe ≤ pr.lamBar / 4 ∧
              ∀ z : EuclideanSpace ℝ (Fin m), (slack A C z).PosSemidef →
                ∑ i, c' i * y i ≤ ∑ i, c' i * z i + 2 * μe * m) ∧
          -- (c)
          (∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
              (ℱ : Filtration ℕ mΩ) (O : ℕ → Ω → Query m → Answer m) (pans : ℝ),
            0 ≤ pans → pans < 1 → IsOracle q A C κ pr.ePA pans μ ℱ O →
            μ {ω | ¬ ∀ t Qt, pfQuery pr c' x μs μe (fun u => O u ω) t = some Qt →
                good Qt (O t ω Qt)} ≤ ENNReal.ofReal (NQ * pans))) ∧
      -- in particular, at q ≥ log n with K = K_q = C′q
      (∀ C' κ0 Γ : ℝ, 0 < C' → 1 ≤ κ0 → 1 < Γ → ∃ C1 c1 : ℝ, 0 < C1 ∧ 0 < c1 ∧
        ∀ (n m : ℕ) (q κ μs μe : ℝ), 1 ≤ m → 2 < q → Real.log n ≤ q → 1 ≤ κ → κ ≤ κ0 →
          0 < μs → 0 < μe → Γ⁻¹ ≤ μe / μs → μe / μs ≤ Γ →
          let pr : PFParams := ⟨c0, ce, Cblk, q, C' * q, κ, m⟩
          (((pr.numP μs μe + 1) * pr.tauBlk : ℕ) : ℝ) ≤ C1 * q ^ 2 * Real.sqrt m ∧
            c1 * q ^ (-(3 : ℝ) / 2) ≤ pr.ePA ∧ pr.ePA ≤ C1 * q ^ (-(3 : ℝ) / 2)) ∧
      -- and likewise at q = Θ(log n) with K = K_{q,n} = C_sc q (1 + √(2 n^{2/(q+2)}))
      (∀ Csc κ0 Γ c₁ c₂ : ℝ, 1 ≤ Csc → 1 ≤ κ0 → 1 < Γ → 0 < c₁ → c₁ ≤ c₂ →
        ∃ C1 c1 : ℝ, 0 < C1 ∧ 0 < c1 ∧
        ∀ (n m : ℕ) (q κ μs μe : ℝ), 1 ≤ m → 2 < q → c₁ * Real.log n ≤ q →
          q ≤ c₂ * Real.log n → 1 ≤ κ → κ ≤ κ0 →
          0 < μs → 0 < μe → Γ⁻¹ ≤ μe / μs → μe / μs ≤ Γ →
          let pr : PFParams :=
            ⟨c0, ce, Cblk, q, Csc * q * (1 + Real.sqrt (2 * (n : ℝ) ^ (2 / (q + 2)))), κ, m⟩
          (((pr.numP μs μe + 1) * pr.tauBlk : ℕ) : ℝ) ≤ C1 * q ^ 2 * Real.sqrt m ∧
            c1 * q ^ (-(3 : ℝ) / 2) ≤ pr.ePA ∧ pr.ePA ≤ C1 * q ^ (-(3 : ℝ) / 2)) := by sorry

end Supplement

end MatrixLewis
