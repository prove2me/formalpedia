-- Prove2me | Theorems.Thm_HardCoreLocalSampling_Local_probability_offspring_envelopes
-- name    : HardCoreLocalSampling.Local.probability_offspring_envelopes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:54:09.085419+00:00
-- url     : https://prove2.me/theorems/5c6d01c5-0ac8-413b-9aa8-e307da31f890
-- title:
--   Lemma 10 — Probability and offspring envelopes
-- statement:
--   Fix $\rho$ from Lemma 7, $\eta$ satisfying (11) and $\tau$ satisfying (12). For every internal subproblem $s$ with centers within $\tau$ of the true messages, there are effective rational envelopes $q_{s,\alpha}\ge|d_{s,\alpha}|$ for the coefficients (14)–(16) satisfying
--
--   $$
--   Q_s:=\sum_\alpha q_{s,\alpha}<1,\qquad\sum_\alpha|\alpha|q_{s,\alpha}\le\kappa:=\rho+\frac g4<1.
--   $$
--
--   For $|\alpha|\ge2$ the envelopes are chosen as $q_{s,\alpha}=(M/\eta)t^{|\alpha|}$. Their degree distribution has an exponential tail, uniformly in $s$.
--
--   The chosen constant mass is exactly $g/8$, and the linear masses are strictly positive dyadic rationals whose sum is at most $\rho+g/8$. The total envelope mass is also bounded by $\rho+5g/16$, as in the proof on printed p.9 (PDF p.10).
--
--   The first bound lets $q_{s,\cdot}$ be a selection probability; the second makes the recursion subcritical.
--
--   Differences from the source:
--   - generalization: the centers of Lemma 9 → any nonnegative rational centers within τ of the true messages; reason: the proof uses only these properties; Lemma 9's centers have them
--   - generalization: η chosen by successive halving and a rational τ from (12) → any η satisfying (11) and any τ satisfying (12); reason: the proof uses only (11) and (12); the halving choice satisfies them
--   - reading: effective rational envelopes → one Computable function of the parameter codes, the child centers and α; reason: uniform computability is the stronger reading; for fixed parameters and a finite grid it would be trivial
-- source:
--   Thomas Chen, STOC 2027 submission #462 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/462.pdf, Lemma 10, eqs. (17)–(18), printed p.8 (PDF p.9)

import Mathlib
import Definitions.Def_HardCoreLocalSampling_Local_Params

namespace HardCoreLocalSampling.Local

/-- Thomas Chen, STOC 2027 submission #462, Lemma 10, printed p.8 (PDF p.9), eqs. (17)–(18).
With `ρ` as in Lemma 7, `η` as in (11), `τ` as in (12), and centers within `τ` of the true
messages, the coefficients (14)–(16) of every internal subproblem have rational envelopes
computed from the parameters and the child centers, with `Q_s < 1`, offspring budget at most
`κ = ρ + g/4`, the form (18) in degree at least two, and a tail uniform in `s`. -/
theorem probability_offspring_envelopes :
    ∃ env : (ℕ × RatCode × RatCode × RatCode × RatCode) × List RatCode × List ℕ → RatCode,
      Computable env ∧
      ∀ (Delta : ℕ) (lam rho eta tau : ℚ), Standing Delta lam →
        IsContractionConstant Delta lam rho → IsEta Delta lam rho eta → IsTau rho eta tau →
        ∃ (C θ : ℝ), 0 ≤ C ∧ 0 ≤ θ ∧ θ < 1 ∧
        ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V),
          MaxDegreeLE G Delta → ∀ (D : Finset V) (v : V), v ∉ D →
            residualDegree G D v ≤ bParam Delta →
            ∀ (cs : ℚ) (ck : Fin (orderedNeighbors G D v).length → ℚ),
              0 ≤ cs → (∀ i, 0 ≤ ck i) →
              |(cs : ℝ) - message G (lam : ℝ) D v| ≤ (tau : ℝ) →
              (∀ i, |(ck i : ℝ) - childMessages G (lam : ℝ) D v i| ≤ (tau : ℝ)) →
              let A : (Fin (orderedNeighbors G D v).length → ℕ) → ℝ :=
                taylorCoeff (Fd (lam : ℝ)) (fun i => (ck i : ℝ))
              let d := normalizedCoeff (eta : ℝ) (cs : ℝ) A
              let q : (Fin (orderedNeighbors G D v).length → ℕ) → ℚ := fun α =>
                ratOfCode (env ((Delta, codeOfRat lam, codeOfRat rho, codeOfRat eta, codeOfRat tau),
                  (List.ofFn ck).map codeOfRat, List.ofFn α))
              q 0 = (1 - rho) / 8 ∧
              (∀ i, 0 < q (Pi.single i 1) ∧
                ∃ (m k : ℕ), q (Pi.single i 1) = (m : ℚ) / 2 ^ k) ∧
              (∑ i, (q (Pi.single i 1) : ℝ)) ≤ (rho : ℝ) + (1 - (rho : ℝ)) / 8 ∧
              (∀ α, |d α| ≤ (q α : ℝ)) ∧
              Summable (fun α => (q α : ℝ)) ∧
              ∑' α, (q α : ℝ) ≤ (rho : ℝ) + 5 * (1 - (rho : ℝ)) / 16 ∧
              ∑' α, (q α : ℝ) < 1 ∧
              Summable (fun α => (mdeg α : ℝ) * (q α : ℝ)) ∧
              ∑' α, (mdeg α : ℝ) * (q α : ℝ) ≤ (rho : ℝ) + (1 - (rho : ℝ)) / 4 ∧
              (∀ α, 2 ≤ mdeg α →
                q α = (MParam Delta lam / eta) * tParam Delta eta ^ mdeg α) ∧
              ∀ k, ∑ α ∈ Finset.Nat.antidiagonalTuple (orderedNeighbors G D v).length k,
                (q α : ℝ) ≤ C * θ ^ k := by sorry

end HardCoreLocalSampling.Local
