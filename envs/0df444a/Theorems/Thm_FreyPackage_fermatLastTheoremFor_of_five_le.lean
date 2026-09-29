-- Prove2me | Theorems.Thm_FreyPackage_fermatLastTheoremFor_of_five_le
-- name    : FreyPackage.fermatLastTheoremFor_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/259b9b6e-a51b-5561-89f5-424a77f96466
-- title:
--   Fermat's Last Theorem for prime exponents p ≥ 5
-- statement:
--   The statement takes a natural number $p$ together with hypotheses that $p$ is prime and that $5 \le p$, and concludes `FermatLastTheoremFor p`, Mathlib's predicate asserting that there are no solutions of $a^p + b^p = c^p$ in positive natural numbers $a, b, c$ (equivalently, by `fermatLastTheoremFor_iff_int`, which is used in the proof, no solutions in nonzero integers). Thus the assertion is exactly Fermat's Last Theorem for the single exponent $p$, under the assumptions that $p$ is a prime at least $5$; no claim is made here about exponents $3$, $4$ or composite exponents, and nothing about elliptic curves, Galois representations or modular forms appears in the statement itself, those notions entering only through the results cited in the proof. The two hypotheses are used solely to feed the construction of a Frey package: the project's structure [`FreyPackage`](def/FLTPrelim_FreyPackage.html#L17) packages nonzero integers $a, b, c$ with a prime $p \ge 5$ satisfying $a^p + b^p = c^p$, $\gcd(a,b) = 1$, $a \equiv 3 \pmod 4$ and $b \equiv 0 \pmod 2$.
--
--   This is Fermat's Last Theorem for prime exponents $p \ge 5$, the case settled by Wiles and Taylor–Wiles via the Frey curve, Ribet's level-lowering theorem and Mazur's irreducibility results; the formal statement is the Mathlib predicate `FermatLastTheoremFor p` for one such exponent rather than the full theorem. It is the sole nonelementary input to [`FLT.fermatLastTheorem`](thm.html#FLT.fermatLastTheorem), which combines it with Mathlib's `FermatLastTheorem.of_odd_primes` (handling the exponent $4$) and `fermatLastTheoremThree` to obtain Fermat's Last Theorem for all exponents $n \ge 3$. Everything else in the development sits below this statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_fermatLastTheoremFor_of_five_le.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open CuspForm ModularFormClass UpperHalfPlane

theorem FreyPackage.fermatLastTheoremFor_of_five_le (p : ℕ) (pp : p.Prime) (hp5 : 5 ≤ p) : FermatLastTheoremFor p := by sorry
