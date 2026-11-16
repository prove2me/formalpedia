-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_noOneComponentCertificate
-- name    : HodgeComputer.FourPlusTwoResidual.noOneComponentCertificate
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T07:42:17.598186+00:00
-- url     : https://prove2.me/theorems/a02c4fa7-a9d5-4c41-bf6d-59d46f8da8f8
-- title:
--   No one-component rational field is a four-plus-two residual certificate
-- statement:
--   Let $F\in\mathbb{C}[a,b,s,c,e,t]$ be the six-variable residual sextic of the Hodge Computer instance four-plus-two-residual, and let $A=a^3c^3$ be the corresponding source, as published in `Definitions.Def_HodgeComputerFourPlusTwoResidual` (id `c341e3ae-c576-40ec-b4a9-1e27c1910aa3`). The coordinates are $(a,b,s,c,e,t)=(X_0,X_1,X_2,Y_0,Y_1,Y_2)$, with official ambient type `AmbientPoly n` for $n=5$ (so six variables). The pole parameter is $q=1$.
--
--   **Claim.** This instance admits no Diamond certificate `Verify F A 6 1 D N Q` whose rational vector field is supported in a single coordinate. Equivalently, there do not exist a coordinate index $i$, a legal denominator $D$, numerators $N$, and a polynomial $Q$, such that `Verify F A 6 1 D N Q` holds and $N_j=0$ for all $j\neq i$.
--
--   The obstruction is algebraic and does not use homogeneity beyond the official `Verify` hypotheses (in particular, the identity and legality `IsRelPrime F D`). Writing $C_u=\partial_u A\cdot\partial_u F-A\cdot\partial_u^2 F$, any one-component certificate would force $F$ to divide $C_u$ in the multivariate polynomial ring. For every coordinate $u$, this divisibility fails: for $u\in\{b,e,s,t\}$ one has $\partial_u A=0$ and a specialization keeping $A$ nonzero makes $C_u$ specialize to a nonzero polynomial of degree at most $4$, while $F$ specializes to a degree-$6$ polynomial; for $u=a$ and $u=c$, the specializations $F\mapsto X^6+2$ and $C_u\mapsto -12X^7$ have a nonzero remainder $24X$.
--
--   This lemma excludes one-component legal rational certificates for the six-variable instance, including arbitrary denominator degree and non-strict defect. It does not prove `HodgeComputer.FourPlusTwoResidual.coreCertificate`, `HodgeComputer.FourPlusTwoResidual.normalChart_residue_solvable`, or the mission goal `HodgeComputer.FourPlusTwoResidual.certificate`; those statements remain open. It also does not by itself exclude one-component strict core solutions: the core equation is different, and a core lift generally creates additional binary components.
--
--   **Formalization note.** The formal statement is the non-existence of $i$, $D$, $N$, and $Q$ such that `Verify F A 6 1 D N Q` holds and $N$ vanishes off the single index $i$. The obstruction was derived from analysis by a better model, relayed by Ethan Cheung, checked with computer algebra, and formalized here.
-- source:
--   Official definition HodgeComputerFourPlusTwoResidual (prove2.me definition id c341e3ae-c576-40ec-b4a9-1e27c1910aa3; official F and A, n=5, d=6, q=1). Instance four-plus-two-residual of Hodge Computer, https://hodge.computer/#case/four-plus-two-residual and github.com/hodge-computer/sextics. The one-component obstruction was derived from analysis by a better model, relayed by Ethan Cheung, checked with computer algebra, and formalized here. This is not a re-upload of xuanji's accepted sketch of the main certificate (submission a963c410-7abf-4947-a8a6-6f0243b839cf), nor of the already accepted lemma HodgeComputer.FourPlusTwoResidual.noLinearStrictField (theorem_id 33bbe514-c080-466c-b7ae-d9cf97b7b763).

import Definitions.Def_HodgeComputerFourPlusTwoResidual
open MvPolynomial
open HodgeComputer
open HodgeComputer.FourPlusTwoResidual

theorem HodgeComputer.FourPlusTwoResidual.noOneComponentCertificate :
    ¬ ∃ (i : Fin (n + 1)) (D : AmbientPoly n)
      (N : Fin (n + 1) → AmbientPoly n) (Q : AmbientPoly n),
        Verify F A 6 1 D N Q ∧ ∀ j, j ≠ i → N j = 0 := by sorry
