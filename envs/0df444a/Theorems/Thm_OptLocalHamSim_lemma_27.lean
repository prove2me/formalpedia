-- Prove2me | Theorems.Thm_OptLocalHamSim_lemma_27
-- name    : OptLocalHamSim.lemma_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:34:49.10923+00:00
-- url     : https://prove2.me/theorems/2a7247ff-47c7-4bdf-8072-e240bdabfa34
-- title:
--   Lemma 27 — restriction of a local evolution: $\|\tau^\Lambda_t(O_X)-\tau^Y_t(O_X)\|\le C_{LR}|X|\|O_X\|e^{-\mu d}$
-- statement:
--   On a lattice of dimension $D\ge1$ with $q\ge1$ data qubits per site, let $H=\sum_Zh_Z$ satisfy Eq. (1) with local strength at most one, let $\nu\ge1$ bound $|Z|$ for every interaction ($h_Z\ne0$), and let $R_{LR}:=\max\{1,R\}$. Write $\tau^Y_t(O):=U_Y(t)^\dagger OU_Y(t)$ with $U_Y(t)=e^{-iH_Yt}$. Let $O_X$ be supported on a nonempty set $X\subseteq Y$, let $|t|\le1$ and $\mu>0$.
--
--   1. If $Y=\Lambda$, then $\tau^\Lambda_t(O_X)=\tau^Y_t(O_X)$.
--   2. Otherwise, with $d:=\mathrm{dist}(X,\Lambda\setminus Y)$ and $C_{LR}:=\exp(2\nu e^{\mu R_{LR}})$,
--
--   $$
--   \bigl\|\tau^\Lambda_t(O_X)-\tau^Y_t(O_X)\bigr\|\le|X|\,\|O_X\|\sum_{q\ge\lceil d/R_{LR}\rceil}\frac{(2\nu|t|)^q}{q!}\le C_{LR}|X|\,\|O_X\|e^{-\mu d}.
--   $$
--
--   This Lieb–Robinson restriction estimate localizes the effect of removed boundary interactions and is the analytic input of Lemma 4. Because every hypothesis survives the removal of interaction terms, the same estimates hold after removing any collection of terms.
--
--   **Formalization Note** The tail series is written as $\sum_{k\ge0}(2\nu|t|)^{k+k_0}/(k+k_0)!$ with $k_0=\lceil d/R_{LR}\rceil$.
--
--   Differences from the source:
--   - reading: If Y = Λ, the difference and the tail are zero → for Y = Λ the difference is zero; the tail is not stated; reason: dist(X, ∅) is undefined, so the zero tail is a convention (d = ∞); the difference is the mathematical content
--   - encoding: ∑_{q≥⌈d/R_LR⌉} → ∑' k : ℕ of the term at index k + ⌈d/R_LR⌉; reason: a reindexing of the same series of nonnegative terms
--   - encoding: The same estimates hold after removing any collection of interaction terms → no separate clause; the statement holds for every h satisfying the hypotheses; reason: removing terms preserves range, support size and local strength, so the clause is an instance of the statement
--   - encoding: H = Σ_{Z⊆Λ} h_Z, each term on a nonempty declared set Z → one matrix h Z for every finite set of sites, with h Z ≠ 0 only on nonempty Z (so h ∅ = 0); reason: several terms on one Z are their sum; no instance changes
-- source:
--   Shen, Wu, Yao, Yuan, Zhang, Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian Simulation, STOC 2027 submission (held version, sha256 44a9768a…), Lemma 27, eq. (176), pp.59–60

import Mathlib
import Definitions.Def_OptLocalHamSim_Site
import Definitions.Def_OptLocalHamSim_IsLocalHam

open scoped Matrix.Norms.L2Operator

namespace OptLocalHamSim

/-- **Lemma 27 (Restriction of a local evolution)**, Shen, Wu, Yao, Yuan, Zhang, *Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian
Simulation*, STOC 2027 submission (held version, sha256 44a9768a…), pp.59–60. Suppose the local strength is at
most one. Let ν ≥ 1 be a fixed upper bound on every interaction support size |Z|, and let
R_LR := max{1, R}. If O_X is supported on a nonempty set X ⊆ Y and d := dist(X, Λ ∖ Y), then for
|t| ≤ 1 and any fixed µ > 0
‖τ^Λ_t(O_X) − τ^Y_t(O_X)‖ ≤ |X|‖O_X‖ ∑_{q≥⌈d/R_LR⌉} (2ν|t|)^q/q! ≤ C_LR|X|‖O_X‖e^{−µd} (176),
where C_LR := exp(2νe^{µR_LR}). If Y = Λ, the difference and the tail are zero.

**Formalization Note**
* `τ^Y_t(O) = U_Y(t)† O U_Y(t)` with `U_Y(t) = e^{−iH_Y t}` (`heis (HamOn h Y) t O`); `τ^Λ` uses
  the full `H`.
* `D ≥ 1` and `q ≥ 1` data qubits per site are the standing assumptions of §1.1, p.4.
* "Every interaction support": every `Z` with `h Z ≠ 0`.
* The tail is the series `∑_{k ≥ 0} (2ν|t|)^{k+k₀}/(k+k₀)!`, `k₀ = ⌈d/R_LR⌉`, a reindexing of
  `∑_{q ≥ k₀}`.
* For `Y = Λ` the distance to the empty complement is undefined; that case is the separate conjunct
  "the difference is zero" (the paper's zero tail is the convention `d = ∞`).
* "The same estimates hold after removing any collection of interaction terms": removing terms
  preserves every hypothesis, and the statement holds for every such `h`. -/
theorem lemma_27 {D q : ℕ} (hD : 1 ≤ D) (hq : 1 ≤ q) (L : Fin D → ℕ) (R : ℝ)
    (h : Finset (Site L) → Matrix (Dat L q → Bool) (Dat L q → Bool) ℂ) (hh : IsLocalHam R 1 h)
    (ν : ℝ) (hν : 1 ≤ ν) (hνZ : ∀ Z, h Z ≠ 0 → (Z.card : ℝ) ≤ ν)
    (X Y : Finset (Site L)) (hX : X.Nonempty) (hXY : X ⊆ Y)
    (O : Matrix (Dat L q → Bool) (Dat L q → Bool) ℂ) (hO : SupportedOn (qubitsOf q X) O)
    (t : ℝ) (ht : |t| ≤ 1) (μ : ℝ) (hμ : 0 < μ) :
    (Y = Finset.univ → heis (Ham h) t O - heis (HamOn h Y) t O = 0) ∧
    (Y ≠ Finset.univ →
      ‖heis (Ham h) t O - heis (HamOn h Y) t O‖ ≤
        (X.card : ℝ) * ‖O‖ * ∑' k : ℕ,
          (2 * ν * |t|) ^ (k + ⌈(setDist X Yᶜ : ℝ) / max 1 R⌉₊) /
            ((k + ⌈(setDist X Yᶜ : ℝ) / max 1 R⌉₊).factorial : ℝ) ∧
      (X.card : ℝ) * ‖O‖ * (∑' k : ℕ,
          (2 * ν * |t|) ^ (k + ⌈(setDist X Yᶜ : ℝ) / max 1 R⌉₊) /
            ((k + ⌈(setDist X Yᶜ : ℝ) / max 1 R⌉₊).factorial : ℝ)) ≤
        Real.exp (2 * ν * Real.exp (μ * max 1 R)) * (X.card : ℝ) * ‖O‖ *
          Real.exp (-(μ * setDist X Yᶜ))) := by sorry

end OptLocalHamSim
