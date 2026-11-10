-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_lemma_7_7
-- name    : KSATSingleFlip.Connect.lemma_7_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:08:00.72483+00:00
-- url     : https://prove2.me/theorems/8d3bfdba-98a0-4bdc-bf83-10de0bde3594
-- title:
--   Lemma 7.7 — bounds for Glauber dynamics: coupled walks stay close; few near-false omitted clauses
-- statement:
--   For sufficiently large $k$ there are $C_k>0$ and $T_k\in\mathbb N$, depending only on $k$, such that for sufficiently large $n$:
--
--   (i) Let $\Psi$ have at most $2^kn$ clauses with independent uniform scopes, and fix $B\subseteq[n]$, an integer $t\ge0$ and $0<r\le n/4$. With probability at least $1-\exp(|B| - r/(C_ke^{C_kt/n}))$, for all $F\subseteq\Psi$ and $z,z'$ agreeing outside $B$, the coupled $t$-step walks from $z,z'$ on $F[z],F[z']$ end within Hamming distance $r$.
--
--   (ii) For fixed $z$, sample $M\sim\mathrm{Pois}(m)$, $\Phi^+\sim\Phi(k,n,M)$; let $X$ be the $t$-step Glauber state on $\Phi^+[z]$ from $z$ and $D$ the clauses of $\Phi^+\setminus\Phi^+[z]$ with at most one true literal under $X$. If $m/n$ lies in (1.2) and $t\ge T_kn$, then for every $s>0$, with probability at least $1-e^{-4\rho^{10}n}-(e\rho^5n/s)^s$, if $\Phi^+$ is regular then $|D|\le s$.
--
--   In Lean the signs of $\Psi$ in (i) are given by an arbitrary rule of the scopes, the probability is over the scopes and the shared update sequence, and the degree cutoff of $\mathsf{Reg}$ in (ii) is an arbitrary $D$ fixed after $C_k$, with $T_k$ chosen after it.
--
--   Differences from the source:
--   - generalization: Ψ with independent uniform scopes (signs left unspecified; uniform in the application) → signs given by an arbitrary rule sg of the whole scope vector; reason: fair independent signs are a mixture of such rules, so the bound for every rule implies the source's; the proof's event depends only on scopes and update coordinates
--   - generalization: Reg with the paper's degree cutoff D_k; T_k depending only on k → ∀ D (any cutoff), ∃ T_k chosen after D (C_k chosen before D); reason: specializes to the paper's D_k; part (ii) inherits Lemma 7.9's T_k
--   - encoding: end within Hamming distance r → d_H ≤ r; reason: "within distance r" is ≤ r
--   - encoding: F ⊆ Ψ → sub-formulas as position sets I of Ψ; F[z] = satBy (subF Ψ I) z; reason: sub-multisets of an indexed collection
--   - encoding: M ∼ Pois(m) and then M independent clauses → poisExp/poisProb: the series ∑_M e^{-m} m^M/M! · (uniform average over M-tuples of clauses); reason: same law; the integrands lie in [0,1], so the series converges
--   - encoding: variables [n] = {1,…,n}, formulas as indexed clause collections → variables Fin n; Φ(k,n,m) = uniform law on the published Formula n k m; other formulas are clause lists (position = clause index), sub-formulas are sets of positions; reason: bijective reindexing; repeated clauses stay distinct, as in the paper's indexed collections
--   - encoding: m ≥ 0 is the mean of the Poisson clause count → m : ℝ with 0 ≤ m; reason: the law in Lemma 7.8 permits every nonnegative real mean, including zero; restricting it to natural means omits these instances
-- source:
--   Wang, Yin, Yu, Zhang (2026), Single-Variable Connectivity in Random k-SAT, arXiv:2611.05981 (held version, SHA-256 1821a501…58b80f5), Lemma 7.7, printed p. 54–55 (PDF 56–57)

import Mathlib
import Definitions.Def_SATComputability
import Definitions.Def_KSATSingleFlip_Connect_Model
import Definitions.Def_KSATSingleFlip_Connect_FactorGraph
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_KSATSingleFlip_Connect_Glauber

open scoped Classical BigOperators
open OAI.FixedClauseThreshold

namespace KSATSingleFlip.Connect

/-- Lemma 7.7 (bounds for Glauber dynamics; printed pp. 54–55). For sufficiently large `k` there
are `C_k > 0` and `T_k ∈ ℕ` (here `T_k` is chosen after the degree cutoff `D` of `Reg`, the paper's
`D_k`, and the statement is made for every value of the cutoff) such that for sufficiently
large `n`:
(i) for `Ψ` with `M ≤ 2^k n` clauses whose scopes are independent uniform `k`-sets (signs given by
an arbitrary rule `sg` of the scopes), `B ⊆ [n]`, `t ≥ 0` and `0 < r ≤ n/4`: with probability at
least `1 − exp(|B| − r/(C_k e^{C_k t/n}))` over the scopes and the update sequence, for all
`F ⊆ Ψ` and `z, z′` agreeing outside `B`, the coupled `t`-step walks from `z, z′` on `F[z]`, `F[z′]`
end within Hamming distance `r`;
(ii) for fixed `z`, `M ∼ Pois(m)`, `Φ⁺ ∼ Φ(k, n, M)`, `X` the `t`-step Glauber state on `Φ⁺[z]` from
`z`, `D` the clauses of `Φ⁺ ∖ Φ⁺[z]` with at most one true literal under `X`, `m/n` in (1.2) and
`t ≥ T_k n`: for every `s > 0`, with probability at least `1 − e^{−4ρ^{10} n} − (eρ^5 n/s)^s`,
`Reg(Φ⁺)` implies `|D| ≤ s`. -/
theorem lemma_7_7 :
    ∃ k0 : ℕ, ∀ k ≥ k0, ∃ Ck : ℝ, 0 < Ck ∧ ∀ D : ℕ, ∃ Tk : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0,
      (∀ M : ℕ, (M : ℝ) ≤ (2 : ℝ) ^ k * n →
        ∀ (sg : (Fin M → {S : Finset (Fin n) // S.card = k}) → Fin M → Fin n → Bool)
          (B : Finset (Fin n)) (t : ℕ) (r : ℝ), 0 < r → r ≤ (n : ℝ) / 4 →
          1 - Real.exp (B.card - r / (Ck * Real.exp (Ck * t / n))) ≤
            uprob fun ω : (Fin M → {S : Finset (Fin n) // S.card = k}) × (Fin t → Fin n × Bool) =>
              let Ψ : GFormula (Fin n) :=
                List.ofFn fun j : Fin M => fun i : Fin n =>
                  if i ∈ (ω.1 j).1 then some (sg ω.1 j i) else none
              ∀ (I : Finset (Fin Ψ.length)) (z z' : Fin n → Bool), (∀ u, u ∉ B → z u = z' u) →
                (hamming (glauberState (satBy (subF Ψ I) z) z ω.2)
                    (glauberState (satBy (subF Ψ I) z') z' ω.2) : ℝ) ≤ r) ∧
      (∀ m : ℝ, 0 ≤ m → m / n ≤ densityBound k gammaStar →
        ∀ (z : Fin n → Bool) (t : ℕ), Tk * n ≤ t → ∀ s : ℝ, 0 < s →
          1 - Real.exp (-4 * rho k ^ 10 * n) - Real.rpow (Real.exp 1 * rho k ^ 5 * n / s) s ≤
            poisExp (allClauses n k) m (fun l =>
              uprob fun seq : Fin t → Fin n × Bool =>
                Reg k D (ofList l) →
                  (((Finset.univ : Finset (Fin (ofList l).length)).filter fun j =>
                      ¬ ClauseSat z ((ofList l).get j) ∧
                        (satSet (glauberState (satBy (ofList l) z) z seq)
                          ((ofList l).get j)).card ≤ 1).card : ℝ) ≤ s)) := by sorry

end KSATSingleFlip.Connect
