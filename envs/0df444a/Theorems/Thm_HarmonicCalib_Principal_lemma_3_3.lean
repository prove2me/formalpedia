-- Prove2me | Theorems.Thm_HarmonicCalib_Principal_lemma_3_3
-- name    : HarmonicCalib.Principal.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:06:34.012684+00:00
-- url     : https://prove2.me/theorems/767b3556-035c-487b-ba3e-4cd023689ae4
-- title:
--   Lemma 3.3 — the three principal examples: $\gamma(B_2,B_2)\le\pi/2$, $\gamma(B_\infty,B_\infty)=\gamma(B_1,B_1)=O(\log d)$; horizons $e^{C/\varepsilon}$ and $d^{C/\varepsilon}$
-- statement:
--   There is an absolute constant $C > 0$ such that for every $d \ge 2$:
--
--   1. $\gamma(B_2^d, B_2^d) \le \pi/2$;
--   2. $\gamma(B_\infty^d, B_\infty^d) = \gamma(B_1^d, B_1^d)$, and $\gamma(B_\infty^d, B_\infty^d) \le C \log d$;
--   3. for every $\varepsilon > 0$, Algorithm 1 attains $\varepsilon$-calibration — $\mathrm{Cal}_{L,T}/T \le \varepsilon$ for every initial forecast $p_{\mathrm{init}} \in Y$ and every outcome sequence $y_0,\dots,y_{T-1} \in Y$ —
--      * for every $T \ge \exp(C/\varepsilon)$ when $Y = L = B_2^d$,
--      * for every $T \ge d^{C/\varepsilon}$ when $Y \in \{[0,1]^d, B_\infty^d\}$ and $L = B_\infty^d$,
--      * for every $T \ge d^{C/\varepsilon}$ when $Y \in \{\Delta_d, B_1^d\}$ and $L = B_1^d$.
--
--   Here $\gamma(Y,L) = \sup_{T\ge1}\Gamma^{(T)}_{Y - c_Y, L^\circ}(K_T)/T$ (in the extended reals) and $\mathrm{Cal}_{L,T}$ is the $L$-calibration error. This is the formal content of Theorem 1.1 (p. 3).
--
--   Differences from the source:
--   - encoding: O(log d) and "for an absolute constant C" (one constant per clause) → one ∃ C > 0, quantified before d, serving the log d bound and all three horizons; reason: O(log d) over d ≥ 2 means ≤ C' log d for an absolute C'; the maximum of the constants serves every clause (log d > 0 and d^{C/ε}, exp(C/ε) increase in C), so the two forms are equivalent
--   - encoding: ℝ^d with the standard inner product → EuclideanSpace ℝ (Fin d) with ⟪·,·⟫_ℝ; reason: the same space; coordinates are x i for i : Fin d
--   - encoding: B_q^d = {x : ‖x‖_q ≤ 1}, [0,1]^d, Δ_d → ballOne, ballTwo, ballInf, unitCube, simplex written coordinatewise; reason: the same sets; Fin d → ℝ's sup norm is not used
--   - encoding: T ≥ exp(C/ε), T ≥ d^{C/ε} → Real.exp (C/ε) ≤ (T : ℝ), (d : ℝ) ^ (C/ε) ≤ (T : ℝ) (rpow), T : ℕ; reason: the same thresholds; no T ≥ 2 hypothesis is added
--   - encoding: every realized transcript (μ_0, y_0), …, (μ_{T-1}, y_{T-1}) against an adaptive adversary → every outcome sequence y : ℕ → ℝ^d with y t ∈ Y for t < T, μ_t = alg1Mu p_init y t; reason: Algorithm 1 is deterministic and μ_t depends only on y_0, …, y_{t-1}, so transcripts and outcome sequences coincide; values of y after round T-1 are never read
--   - encoding: finite distributions μ_t over forecasts, Cal summed over distinct points with positive total weight → μ_t : ℝ^d →₀ ℝ (equal points are one key) and calError sums over the points of the supports with ∑_t μ_t(p) > 0, norm gauge L; reason: the same quantity; aggregation of equal forecast values is automatic
--   - encoding: Γ^{(T)} and γ as real suprema → Gamma and gammaCoef valued in EReal (iSup); reason: an EReal supremum is never a junk value; on nonempty compact sets Γ is finite and the EReal comparison is the real one
-- source:
--   Fishelson and Mohri (2026), High-Dimensional Online Calibration from Harmonic Weights, arXiv:2610.07740 (version dated October 29, 2026; PDF SHA256 62ac31a3…), Lemma 3.3, p. 14 (formal content of Theorem 1.1, p. 3)

import Mathlib
import Definitions.Def_HarmonicCalib_Principal_Geometry
import Definitions.Def_HarmonicCalib_Principal_Discrepancy
import Definitions.Def_HarmonicCalib_Principal_Calibration

namespace HarmonicCalib.Principal

/-- Lemma 3.3 (the three principal examples, p. 14), every clause, with one absolute constant `C`
chosen before `d`: for every `d ≥ 2`,
* `γ(B_2^d, B_2^d) ≤ π/2`;
* `γ(B_∞^d, B_∞^d) = γ(B_1^d, B_1^d)` and `γ(B_∞^d, B_∞^d) ≤ C log d`;
and Algorithm 1 attains `ε`-calibration (`Cal_{L,T}/T ≤ ε` for every `p_init ∈ Y` and every
outcome sequence in `Y`) for every `ε > 0` and
* every `T ≥ exp(C/ε)` if `Y = L = B_2^d`,
* every `T ≥ d^{C/ε}` if `Y ∈ {[0,1]^d, B_∞^d}` and `L = B_∞^d`,
* every `T ≥ d^{C/ε}` if `Y ∈ {Δ_d, B_1^d}` and `L = B_1^d`. -/
theorem lemma_3_3 :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      gammaCoef (ballTwo d) (ballTwo d) ≤ ((Real.pi / 2 : ℝ) : EReal) ∧
      gammaCoef (ballInf d) (ballInf d) = gammaCoef (ballOne d) (ballOne d) ∧
      gammaCoef (ballInf d) (ballInf d) ≤ ((C * Real.log d : ℝ) : EReal) ∧
      (∀ ε : ℝ, 0 < ε → ∀ T : ℕ, Real.exp (C / ε) ≤ (T : ℝ) →
        ∀ pinit ∈ ballTwo d, ∀ y : ℕ → EuclideanSpace ℝ (Fin d),
          (∀ t, t < T → y t ∈ ballTwo d) → alg1Cal (ballTwo d) T pinit y / T ≤ ε) ∧
      (∀ Y ∈ ({unitCube d, ballInf d} : Set (Set (EuclideanSpace ℝ (Fin d)))),
        ∀ ε : ℝ, 0 < ε → ∀ T : ℕ, (d : ℝ) ^ (C / ε) ≤ (T : ℝ) →
        ∀ pinit ∈ Y, ∀ y : ℕ → EuclideanSpace ℝ (Fin d),
          (∀ t, t < T → y t ∈ Y) → alg1Cal (ballInf d) T pinit y / T ≤ ε) ∧
      (∀ Y ∈ ({simplex d, ballOne d} : Set (Set (EuclideanSpace ℝ (Fin d)))),
        ∀ ε : ℝ, 0 < ε → ∀ T : ℕ, (d : ℝ) ^ (C / ε) ≤ (T : ℝ) →
        ∀ pinit ∈ Y, ∀ y : ℕ → EuclideanSpace ℝ (Fin d),
          (∀ t, t < T → y t ∈ Y) → alg1Cal (ballOne d) T pinit y / T ≤ ε) := by sorry

end HarmonicCalib.Principal
