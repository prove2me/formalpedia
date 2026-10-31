-- Prove2me | Theorems.Thm_MayersBC_binary_kolmogorov_eq
-- name    : MayersBC.binary_kolmogorov_eq
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:57:14.751442+00:00
-- url     : https://prove2.me/theorems/6e00f4fb-e626-43fc-8412-927f0c4ad5ae
-- title:
--   Section d, p.7 — for a binary guess, $K(p_0,p_1) = 4\,|\mathrm{PE} - \tfrac12|$
-- statement:
--   Let $\rho_0, \rho_1$ be density matrices and let $Q$ be an effect ($0 \le Q \le I$). Let $p_b$ be the outcome distribution of the two-outcome measurement $\{Q, I - Q\}$ on $\rho_b$, and let $\mathrm{PE}$ be the probability of error of the guess "$0$ on outcome $Q$, $1$ on outcome $I-Q$" for a uniformly random bit. Then
--
--   $$
--   K(p_0, p_1) = 4\,\big|\mathrm{PE} - \tfrac12\big| ,
--   $$
--
--   where $K$ is the Kolmogorov distance without the factor $\tfrac12$. In particular Bob's criterion $|\mathrm{PE} - \tfrac12| \le \varepsilon$ gives $K(p_0, p_1) \le 4\varepsilon$ for every binary measurement.
--
--   Differences from the source:
--   - generalization: the criterion |PE − 1/2| ≤ ε implies K(p0, p1) ≤ 4ε → the identity K(p0, p1) = 4|PE − 1/2|; reason: the identity gives the implication for every ε; it is the 'some algebra' of the page
--   - encoding: Bob's guess X from a measurement with two outcomes → the measurement binaryPOVM Q = {Q, I − Q} with guess 0 on outcome Q; reason: a two-outcome guess is exactly such a measurement
-- source:
--   Mayers, The Trouble with Quantum Bit Commitment, arXiv:quant-ph/9603015v3, section d, p.7

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_MayersBC_guessError
import Definitions.Def_MayersBC_outcomeDist
import Definitions.Def_MayersBC_binaryPOVM
import Definitions.Def_MayersBC_kolmogorov
open QAlgorithms

namespace MayersBC

/-- Mayers, *The Trouble with Quantum Bit Commitment*, arXiv:quant-ph/9603015v3, section d, p.7:
"After some algebra, one obtains that the criteria |PE − 1/2| ≤ ε implies that K(p0, p1) ≤ 4ε."
For density matrices `ρ_0, ρ_1` and a two-outcome measurement `{Q, I − Q}`, the Kolmogorov
distance (no ½) between the two outcome distributions equals `4 |PE − ½|`, where `PE` is the
error of the guess "`0` on `Q`, `1` on `I − Q`" for a uniformly random bit.

**Formalization Note.** Stated as the identity behind "after some algebra", which gives the
implication `|PE − ½| ≤ ε → K ≤ 4ε` for every `ε`. Trace one of both states is used. -/
theorem binary_kolmogorov_eq {ι : Type} [Fintype ι] [DecidableEq ι] (ρ0 ρ1 Q : Matrix ι ι ℂ)
    (h0 : IsDensityMatrix ρ0) (h1 : IsDensityMatrix ρ1) (hQ : IsEffect Q) :
    kolmogorov (outcomeDist (binaryPOVM Q) ρ0) (outcomeDist (binaryPOVM Q) ρ1) =
      4 * |guessError ρ0 ρ1 Q - 1 / 2| := by sorry

end MayersBC
