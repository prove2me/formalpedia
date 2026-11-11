-- Prove2me | Theorems.Thm_LowRankShifts_MatPoly_section_2_5_eq_1
-- name    : LowRankShifts.MatPoly.section_2_5_eq_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:57:13.251376+00:00
-- url     : https://prove2.me/theorems/117add37-dc60-410f-9fba-b277001f7970
-- title:
--   §2.5, Eq. (1) — the Fourier transform of an average of shifts is the product of the transforms
-- statement:
--   Let $p$ be a prime, $f:\mathbb F_p^{n\times m}\to\mathbb C$, and $D$ a probability distribution on $\mathbb F_p^{n\times m}$ with probability mass function $\mu(X)=\Pr_{Y\sim D}[Y=X]$. If $q(A)=\mathbb E_{X\sim D}[f(A-X)]$, then for every $W\in\mathbb F_p^{n\times m}$
--
--   $$\hat q(W)=\hat f(W)\,\hat\mu(W),$$
--
--   with the Fourier transform $\hat g(W)=\sum_X g(X)\,\omega_p^{-\langle W,X\rangle}$ of the definition `LowRankShifts_MatPoly_Fourier`.
--
--   This is the convolution theorem in the form the proof of Lemma 3.2 uses, with $D$ the law of $UV^T$.
--
--   **Formalization Note.** $D$ is a `PMF` on matrices; $q(A)=\sum_X D(X)\,f(A-X)$ and $\mu(X)=D(X)$ as complex numbers.
--
--   Differences from the source:
--   - encoding: q(A) := E_{X∼D}[f(A − X)], µ(X) := Pr_{Y∼D}[Y = X] → `D : PMF (Matrix …)`, q(A) = Σ_X D(X)·f(A − X) and µ(X) = D(X), cast to ℂ; reason: the expectation over a finite probability space as a weighted sum
--   - encoding: ω_p^{−⟨W,X⟩} with ω_p = e^{2πi/p} → `omegaInvPow (frob W X) = exp(−2πi·(frob W X).val/p)`; reason: the canonical representative in {0, …, p−1}; the same complex number
-- source:
--   Golovnev, Nagargoje, Shinkar, Singh, Stephens-Davidowitz, Worst-Case to Average-Case Reductions for Linear Algebra: Optimal, Simple, and General, STOC 2027 submission (manuscript sha256 ebcf9677…), p. 15 (PDF 18), §2.5, Eq. (1)

import Mathlib
import Definitions.Def_LowRankShifts_MatPoly_Fourier

set_option autoImplicit false

namespace LowRankShifts.MatPoly

/-- §2.5, Eq. (1) (p. 15): if `q(A) := E_{X∼D}[f(A − X)]` for a probability distribution `D` on
`F_p^{n×m}`, then `q̂(W) = f̂(W) µ̂(W)`, where `µ(X) := Pr_{Y∼D}[Y = X]`. -/
theorem section_2_5_eq_1 {p : ℕ} [Fact p.Prime] {n m : ℕ}
    (D : PMF (Matrix (Fin n) (Fin m) (ZMod p))) (f : Matrix (Fin n) (Fin m) (ZMod p) → ℂ)
    (W : Matrix (Fin n) (Fin m) (ZMod p)) :
    fourier (fun A => ∑ X, ((D X).toReal : ℂ) * f (A - X)) W =
      fourier f W * fourier (fun X => ((D X).toReal : ℂ)) W := by sorry

end LowRankShifts.MatPoly
