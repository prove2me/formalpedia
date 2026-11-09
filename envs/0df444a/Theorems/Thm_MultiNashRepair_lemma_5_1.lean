-- Prove2me | Theorems.Thm_MultiNashRepair_lemma_5_1
-- name    : MultiNashRepair.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:33:05.519723+00:00
-- url     : https://prove2.me/theorems/9af2ddf1-f81b-4f36-ade9-17668d995d5c
-- title:
--   Lemma 5.1 — descent bound (5.10) and failed-dual columns (5.11)–(5.12) (carries Proposition 4.1)
-- statement:
--   Let $x$ be a mixed profile of an $m$-player game ($m\ge1$) with payoffs in $[0,1]$, let $0<\eta<1$, $\mu>0$, and $\varsigma=m(1-\mathrm{Reg}(x))$.
--
--   1. **Passing direction.** Let $z$ be feasible with LP objective at most $\mathrm{Reg}(x)-\eta\mu/m$. Put $Z_j=\sum_bz_{j,b}$, $Z=\sum_jZ_j\le1$, $P=\prod_j(1-\eta Z_j)$ and $x^+_j=(1-\eta Z_j)x_j+\eta\sum_bz_{j,b}e_b$. Then
--   $$\varsigma^+\ge P\bigl[(1+\eta Z)\varsigma+\eta\mu\bigr]\ge\varsigma+\eta\mu-\eta^2(\varsigma+\mu)\qquad(5.10),$$
--   and every stored historical mass may be multiplied by $P$: the law of $x^+$ dominates $P$ times the law of $x$, the same holds for every opponent override $x[j\leftarrow y_j]$, and hence any certificate law at $x$ holds at $x^+$ with all masses multiplied by $P$.
--   2. **Failure case.** If the LP fails, every optimal dual gives a probability vector $\lambda$ and mixed deviations $b_i$ such that for every player $j$ and every mixed $y_j$
--   $$F_j(y_j)=\sum_i\lambda_i\,d_{i,b_i}(x[j\leftarrow y_j])<\frac{\varsigma+\mu}{m}\qquad(5.11),$$
--   and $\lambda_j\le F_j(b_j)$, $\ \sum_i\lambda_id_{i,b_i}(x)<(\varsigma+\eta\mu)/m$ (5.12).
--
--   Part 1 is Proposition 4.1 (p.11). The columns (5.11) are the input of the repair analysis.
--
--   Differences from the source:
--   - generalization: the selected optimal rational LP solution $z$ → every feasible $z$ whose objective is at most $\mathrm{Reg}(x)-\eta\mu/m$; reason: the proof uses only the passing inequality; contains the optimal solution
--   - generalization: a rational optimal dual → every optimal dual $(w,\alpha)$; reason: the proof uses only dual feasibility and strong duality
--   - generalization: rational $0<\eta<1$, $\mu>0$ → real $0<\eta<1$, $\mu>0$; reason: contains the rational case
--   - reading: every stored historical mass may be multiplied by $P$ → domination of the laws of $x^+$ and of every override by $P$ times those of $x$, and preservation of `CertLaw` with masses times $P$; reason: Lemma 5.2 (C3) in measure form
--   - encoding: an optimal dual → `DualFeasible` with objective equal to the LP value; reason: strong duality
--   - generalization: game with rational payoffs in $[0,1]$ → any real game with payoffs in $[0,1]$ (`BoundedGame`); reason: the proof uses only $0\le u_i\le1$; contains the paper's rational games
-- source:
--   J. Tang, S. Ding, C. Fang, Breaking the One-Player Extension Barrier: History-Aware Repair for Multiplayer Approximate Nash Equilibria, arXiv:2611.06076 (preprint; held version, sha256 34b911ed…5c14), Lemma 5.1, (5.10)–(5.12), p.17; Proposition 4.1, p.11; Lemma 5.2 (C3), p.20

import Mathlib
import Definitions.Def_NashAmplification_Filtering_Model
import Definitions.Def_MultiNashRepair_DescentLP
import Definitions.Def_MultiNashRepair_Generation
import Definitions.Def_MultiNashRepair_Sweeps

open NashAmplification.Filtering (Mixed Utility Tuple BoundedGame)
open Finset

namespace MultiNashRepair

/-- **Lemma 5.1 (Descent and Failed-Dual Columns)**, which also carries Proposition 4.1
(Tang, Ding, Fang, arXiv:2611.06076, Lemma 5.1 and (5.12), p.17; Proposition 4.1, p.11;
Lemma 5.2 (C3), p.20).

Let `x` be a mixed profile of an `m`-player game with payoffs in `[0,1]`, `0 < η < 1`, `µ > 0`,
and `ς = m(1 − Reg(x))`.

(a) *Passing direction.* For every feasible `z` with LP objective at most `Reg(x) − η µ/m`, put
`Z = Σ_{j,b} z_{j,b}`, `P = Π_j (1 − η Z_j)` and `x⁺` the descent profile (3.2). Then
`ς⁺ ≥ P[(1 + ηZ)ς + ηµ] ≥ ς + ηµ − η²(ς + µ)` (5.10), and every stored historical mass may be
multiplied by `P`: the law of `x⁺` (and of each override `x⁺[j ← y]`) dominates `P` times the law
of `x` (of `x[j ← y]`), so the certificate law of any list of generations is kept with masses
multiplied by `P`.

(b) *Failure case.* If the LP fails, every optimal dual `(w, α)` gives a probability vector `λ`
and mixed deviations `b_i` ((3.4)) with `F_j(y_j) < (ς + µ)/m` for every player `j` and every
mixed `y_j` (5.11), `λ_j ≤ F_j(b_j)` and `Σ_i λ_i d_{i,b_i}(x) < (ς + ηµ)/m` (5.12).

**Formalization Note.** (a) holds for every feasible `z` passing the test, in particular the
optimal rational one; (b) for every optimal dual, in particular a rational one. `η`, `µ` are
real (the paper's are rational). -/
theorem lemma_5_1 {m : ℕ} {n : Fin m → ℕ} (hm : 1 ≤ m) (hn : ∀ i, 0 < n i)
    (u : Utility n) (hu : BoundedGame u) (x : Mixed n) (hx : AGT.IsMixedProfile x)
    (η mu : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hmu : 0 < mu) :
    (∀ z : (j : Fin m) → Fin (n j) → ℝ, LPFeasible z → lpObj u x η z ≤ Reg u x - η * mu / m →
      let Z := ∑ j, ∑ b, z j b
      let P := descentFactor η z
      let xp := descentProfile x η z
      P * ((1 + η * Z) * scaled u x + η * mu) ≤ scaled u xp ∧
        scaled u x + η * mu - η ^ 2 * (scaled u x + mu) ≤
          P * ((1 + η * Z) * scaled u x + η * mu) ∧
        (∀ a : Tuple n, P * AGT.profileProb x a ≤ AGT.profileProb xp a) ∧
        (∀ (j : Fin m) (y : Fin (n j) → ℝ), AGT.IsLottery y → ∀ a : Tuple n,
          P * AGT.profileProb (Function.update x j y) a ≤
            AGT.profileProb (Function.update xp j y) a) ∧
        ∀ gs : List (Gen n), CertLaw x gs →
          CertLaw xp (gs.map fun g => { g with A := P * g.A })) ∧
    (¬ LPPasses u x η mu → ∀ (w : (i : Fin m) → Fin (n i) → ℝ) (α : ℝ),
      DualOptimal u x η w α →
        AGT.IsLottery (lam w) ∧ AGT.IsMixedProfile (bdev w) ∧
        (∀ (j : Fin m) (y : Fin (n j) → ℝ), AGT.IsLottery y →
          Fcol u x w j y < (scaled u x + mu) / m) ∧
        (∀ j, lam w j ≤ Fcol u x w j (bdev w j)) ∧
        ∑ i, lam w i * deficitMix u x i (bdev w i) < (scaled u x + η * mu) / m) := by sorry

end MultiNashRepair
