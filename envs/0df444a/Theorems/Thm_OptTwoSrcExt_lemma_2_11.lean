-- Prove2me | Theorems.Thm_OptTwoSrcExt_lemma_2_11
-- name    : OptTwoSrcExt.lemma_2_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:26:25.309095+00:00
-- url     : https://prove2.me/theorems/46e02c48-38e2-4a2d-83df-dee04ae343e8
-- title:
--   Lemma 2.11 — Fourier distance bound $\Delta(P,Q)\le\frac12\|\hat P-\hat Q\|_2$
-- statement:
--   Let $P,Q$ be laws on $\mathbb F_2^m$ with Fourier coefficients $\hat P(\lambda)=\mathbb E_{Z\sim P}(-1)^{\lambda\cdot Z}$.
--
--   1. $$\Delta(P,Q)\le\frac12\Big(\sum_{\lambda\in\mathbb F_2^m}|\hat P(\lambda)-\hat Q(\lambda)|^2\Big)^{1/2}.$$
--   2. If every nonzero character of $P$ has bias at most $\beta$ (that is, $|\hat P(\lambda)|\le\beta$ for $\lambda\ne0$, with $\beta\ge0$), then $\Delta(P,U_m)\le2^{m/2}\beta/2$.
--   3. If the law $P$ of a pair $(A,B)$ on $\mathbb F_2^a\times\mathbb F_2^v$ is compared with $(U_a,B)$ ($U_a$ uniform and independent of $B$), only characters with a nonzero $A$ coefficient contribute:
--   $$\Delta\big(P,\ U_a\otimes\mathcal L(B)\big)\le\frac12\Big(\sum_{\lambda\ne0}\sum_{\mu}\hat P(\lambda,\mu)^2\Big)^{1/2}.$$
--
--   This is the tool that converts the character-bias bounds of the paper into statistical-distance bounds.
--
--   Differences from the source:
--   - reading: every nonzero character of P has bias at most β → 0 ≤ β and |P̂(λ)| ≤ β for every λ ≠ 0; reason: a bias bound is nonnegative; at m = 0 a negative β would make the printed inequality false
--   - reading: only characters with a nonzero A coefficient contribute → the bound of clause 1 for Q = U_a ⊗ L(B), with the λ = 0 terms (which vanish) removed; reason: the ideal law has coefficient 0 at λ ≠ 0 and the same coefficient as P at λ = 0
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Lemma 2.11, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic
import Definitions.Def_LowErrExt_indepPair
import Definitions.Def_OptTwoSrcExt_fourier

open FuzzyExtractors.Hamming LowErrExt

namespace OptTwoSrcExt

/-- **Lemma 2.11 (Fourier distance).**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Lemma 2.11, printed p.17 (PDF p.19): "Let P, Q be laws on
F_2^m, and write P̂(λ) = E_{Z∼P}(−1)^{λ·Z}. Then ∆(P, Q) ⩽ ½ (Σ_{λ∈F_2^m} |P̂(λ) − Q̂(λ)|²)^{1/2}. In
particular, if every nonzero character of P has bias at most β, then ∆(P, Um) ⩽ 2^{m/2}β/2. If
(A, B) is compared with (Ua, B), only characters with a nonzero A coefficient contribute."

The three clauses, in order:
1. for all laws `P, Q` on `𝔽₂^m`, `Δ(P, Q) ≤ ½ (∑_λ (P̂(λ) − Q̂(λ))²)^{1/2}`;
2. if `0 ≤ β` and `|P̂(λ)| ≤ β` for every `λ ≠ 0`, then `Δ(P, U_m) ≤ 2^{m/2} β / 2`;
3. for a law `P` of a pair `(A, B)` on `𝔽₂^a × 𝔽₂^v`, comparing with `(U_a, B)` (with `U_a` uniform
   and independent of `B`, and `B` with its actual marginal), only the characters `(λ, μ)` with
   `λ ≠ 0` contribute: `Δ(P, U_a ⊗ L(B)) ≤ ½ (∑_{λ ≠ 0} ∑_μ P̂(λ, μ)²)^{1/2}`.

**Formalization Note.** Clause 3 is the bound of clause 1 for this comparison: the ideal law has
coefficient `0` at `λ ≠ 0` and the same coefficient as `P` at `λ = 0`. The bias bound `β` is a
nonnegative real (at `m = 0` there is no nonzero character and the conclusion reads `0 ≤ β/2`). -/
theorem lemma_2_11 (m : ℕ) :
    (∀ P Q : PMF (Fin m → ZMod 2),
      statDist P Q ≤ 1 / 2 * Real.sqrt (∑ l : Fin m → ZMod 2, (fourier P l - fourier Q l) ^ 2)) ∧
    (∀ (P : PMF (Fin m → ZMod 2)) (β : ℝ), 0 ≤ β →
      (∀ l : Fin m → ZMod 2, l ≠ 0 → |fourier P l| ≤ β) →
        statDist P (PMF.uniformOfFintype (Fin m → ZMod 2)) ≤ (2 : ℝ) ^ ((m : ℝ) / 2) * β / 2) ∧
    (∀ (a v : ℕ) (P : PMF ((Fin a → ZMod 2) × (Fin v → ZMod 2))),
      statDist P (indepPair (PMF.uniformOfFintype (Fin a → ZMod 2)) (P.map Prod.snd)) ≤
        1 / 2 * Real.sqrt (∑ l : Fin a → ZMod 2, ∑ μ : Fin v → ZMod 2,
          if l = 0 then 0 else fourierPair P l μ ^ 2)) := by sorry

end OptTwoSrcExt
