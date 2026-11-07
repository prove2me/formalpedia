-- Prove2me | Theorems.Thm_MatrixSpencer_eq_2_9_2_10
-- name    : MatrixSpencer.eq_2_9_2_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:47:58.257223+00:00
-- url     : https://prove2.me/theorems/8fed6f23-6948-40d5-a159-58e31f8dd412
-- title:
--   Eqs. (2.9)–(2.10), pp.9–10 — $F=\log Z_t$ is $C^1$ with $F'(t)=-\mathbb E_{\mu_t}\mathrm{Tr}(v'(B_t)Y)$, the resolvent form, and the lower bound on $F'$
-- statement:
--   Assume (2.2), and let $M_1,\dots,M_n$ be symmetric with $\sum_iM_i^2\preceq\eta I$. Let $B_t$, $Y$, $Z_t$ be as in Theorem 2.5, $d\mu_t\propto e^{-V(B_t)}d\gamma_n$, and $R_t=(I-B_t)^{-1}$. For $t\in[0,1]$, $Z_t>0$ and $F=\log Z_t$ is continuously differentiable with
--
--   1. $F'(t)=-\mathbb E_{\mu_t}\mathrm{Tr}(v'(B_t)Y)$;
--   2. $-F'(t)=2\beta\,\mathbb E_{\mu_t}\mathrm{Tr}(R_tB_tY)+2(\alpha-\beta)\mathbb E_{\mu_t}\mathrm{Tr}(R_tB_t^{2p-1}Y)$;
--   3. $F'(t)\ge-4\sqrt6\,\beta d\eta-4\sqrt2\,(\alpha-\beta)d(2p\eta)^p$.
--
--   Together with (2.8), integrating $F'$ over $[0,1]$ gives Theorem 2.5.
--
--   **Formalization Note** The derivative is stated within $[0,1]$. The integrands are stated integrable.
--
--   Differences from the source:
--   - reading: M₁,…,Mₙ ∈ ℝ^{d×d} (no word "symmetric") → the Mᵢ are symmetric; reason: ⪯ and V(X) = Tr v(X) are defined for symmetric matrices only (p.6, p.8), and the only use of the statement has symmetric Mᵢ
--   - encoding: V = +∞ outside the unit ball → the real weight e^{−V} is 0 there; reason: the value +∞ is never computed with
--   - encoding: "continuously differentiable" on [0,1] → HasDerivWithinAt on the closed interval plus ContinuousOn of the derivative; reason: the page's range of t is [0, 1]; a two-sided derivative is not defined at the endpoints by the page
--   - encoding: E_{µ_t} implicitly well defined, Z_t > 0 implicit → Z_t > 0 and integrability of the three integrands are in the conclusion; reason: so no junk value of log, / or the integral is read
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), proof of Theorem 2.5, Step 2, p.9 (PDF p.11), and Step 3, (2.9), (2.10), p.10 (PDF p.12)

import Mathlib
import Definitions.Def_MatrixSpencer_Param22
import Definitions.Def_MatrixSpencer_tiltExp
import Definitions.Def_MatrixSpencer_offSeries
import Definitions.Def_MatrixSpencer_vPrimeMat
import Definitions.Def_MatrixSpencer_resolvent

namespace MatrixSpencer

/-- **Regularity of `F` and the identities (2.9), (2.10), proof of Theorem 2.5, Steps 2–3.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), proof of Theorem 2.5, p.9 (PDF p.11), Step 2: "F = log Z_t is continuously differentiable, and
F′(t) = −E_{µ_t} Tr(v′(B_t)Y)"; p.10 (PDF p.12), Step 3: "−F′(t) = 2βE_{µ_t} Tr(R_tB_tY) +
2(α − β)E_{µ_t} Tr(R_tB_t^{2p−1}Y). (2.9)" and "F′(t) ≥ −4√6 βdη − 4√2 (α − β)d(2pη)^p (2.10)".

**Formalization Note.** `Z_t` is `partition`, `E_{µ_t}` is `tiltExp`, `R_t` is `resolvent (B_t)`.
`Z_t > 0` is part of the conclusion, so `F = log Z_t` is not Lean's `log 0 = 0`. The derivative is
within `[0, 1]`, the page's range of `t`, and stated by `HasDerivWithinAt`, never by a junk `deriv`.
Integrability of the three integrands is part of the conclusion. "Continuously differentiable" is the
derivative statement plus continuity of the derivative on `[0, 1]`. -/
theorem eq_2_9_2_10 {n d : ℕ} (α β : ℝ) (p : ℕ) (η : ℝ) (h : Param22 α β p η)
    (M : Fin n → Matrix (Fin d) (Fin d) ℝ) (hM : ∀ i, (M i).IsSymm)
    (hV : (η • (1 : Matrix (Fin d) (Fin d) ℝ) - ∑ i, M i ^ 2).PosSemidef) :
    let dF : ℝ → ℝ := fun t =>
      -tiltExp α β p M t fun g => (vPrimeMat α β p (interp M t g) * offSeries M g).trace
    ContinuousOn dF (Set.Icc 0 1) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      0 < partition α β p M t ∧
      MeasureTheory.Integrable (fun g => (vPrimeMat α β p (interp M t g) * offSeries M g).trace *
        weight α β p (interp M t g)) (gam n) ∧
      MeasureTheory.Integrable (fun g => (resolvent (interp M t g) * interp M t g *
        offSeries M g).trace * weight α β p (interp M t g)) (gam n) ∧
      MeasureTheory.Integrable (fun g => (resolvent (interp M t g) * interp M t g ^ (2 * p - 1) *
        offSeries M g).trace * weight α β p (interp M t g)) (gam n) ∧
      HasDerivWithinAt (fun s => Real.log (partition α β p M s)) (dF t) (Set.Icc 0 1) t ∧
      -dF t =
        2 * β * tiltExp α β p M t (fun g =>
          (resolvent (interp M t g) * interp M t g * offSeries M g).trace) +
        2 * (α - β) * tiltExp α β p M t (fun g =>
          (resolvent (interp M t g) * interp M t g ^ (2 * p - 1) * offSeries M g).trace) ∧
      -(4 * √6) * β * d * η - 4 * √2 * (α - β) * d * (2 * p * η) ^ p ≤ dF t := by sorry

end MatrixSpencer
