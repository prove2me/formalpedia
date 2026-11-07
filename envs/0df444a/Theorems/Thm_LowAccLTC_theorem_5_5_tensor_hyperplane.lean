-- Prove2me | Theorems.Thm_LowAccLTC_theorem_5_5_tensor_hyperplane
-- name    : LowAccLTC.theorem_5_5_tensor_hyperplane
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:37:30.013431+00:00
-- url     : https://prove2.me/theorems/d9e294f1-8271-4437-b6c6-5ec191c2aad1
-- title:
--   Theorem 5.5 [CMS17] — $B^{\otimes k}$ is a $(\Delta^k/12,\ x\mapsto\frac{12}{\Delta^k}x)$-HA LTC under the hyperplane test
-- statement:
--   Let $B\subseteq\mathbb F^n$ be a linear code over a finite field $\mathbb F$ with relative distance $\Delta\in(0,1]$. Then for every $k\ge3$, the tensor code $B^{\otimes k}$ is a
--   $$\Big(\frac{\Delta^k}{12},\ x\mapsto\frac{12}{\Delta^k}x\Big)\text{-HA LTC}$$
--   w.r.t. the hyperplane test: whenever the average distance of $f$ from $B^{\otimes(k-1)}$ on a random axis-parallel hyperplane is $x\le\Delta^k/12$, we have $\mathrm{dist}(f,B^{\otimes k})\le\frac{12}{\Delta^k}x$.
--
--   In the paper this is applied to $B=C_0^{\otimes j}$ on colour-restricted complexes of tensor codes, and its components appear in the analysis of the co-rank-two links of KMS codes (Claim 5.12).
--
--   Differences from the source:
--   - encoding: B has relative distance Δ → 0 < Δ ≤ 1 and distinct codewords differ on ≥ a Δ-fraction of coordinates; reason: a code with two distinct codewords has relative distance in (0,1], and the conclusion is monotone in Δ, so the lower-bound form is equivalent to the exact-value form for every Δ ≤ δ(B)
--   - reading: 'a linear code' (field not named) → a linear subspace of F^n over a finite field F; reason: the paper's codes are over finite fields F_q (Example 2.18)
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), Theorem 5.5 ([CMS17]), p.45 (PDF p.48)

import Definitions.Def_LowAccLTC_tensorCode

namespace LowAccLTC

/-- **Theorem 5.5** (Local testability of tensor codes [CMS17]; Ben Yaacov–Dikstein–Liu, *Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs* (manuscript, sha256 04242e17…), p.45 = PDF p.48).

Let `B ⊆ Fⁿ` be a linear code over a finite field `F` with relative distance `Δ ∈ (0, 1]`. Then
for every `k ≥ 3`, `B^{⊗k}` is a `(Δ^k/12, x ↦ (12/Δ^k) x)`-HA LTC w.r.t. the hyperplane test.

**Formalization Note.** "Relative distance `Δ`" is used as a lower bound (any two distinct
codewords differ on at least a `Δ`-fraction of coordinates); the statement is monotone in `Δ`. -/
theorem theorem_5_5_tensor_hyperplane {F : Type*} [Field F] [Fintype F] (n : ℕ)
    (B : Submodule F (Fin n → F)) (Δ : ℝ) (hΔ : 0 < Δ ∧ Δ ≤ 1) (hB : HasRelDistAtLeast B Δ)
    (k : ℕ) (hk : 3 ≤ k) :
    IsHALTCHyperplane B k (Δ ^ k / 12) (fun x => 12 / Δ ^ k * x) := by sorry

end LowAccLTC
