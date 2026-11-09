-- Prove2me | Theorems.Thm_GroupIsoPoly_charSeries_srad
-- name    : GroupIsoPoly.charSeries_srad
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:54:39.287188+00:00
-- url     : https://prove2.me/theorems/66b63559-3565-47b2-b32c-6715b226b525
-- title:
--   §9.2.1 — the series (9.3) passes through $\mathrm{srad}(Q)$ with elementary abelian factors below it
-- statement:
--   Let $Q$ be a finite group with the series $1=N_0<N_1<\cdots<N_\ell=Q$ of §9.2.1. There is an index $j\le\ell$ with $N_j=\mathrm{srad}(Q)$ such that
--   1. for every $i<j$ the factor $N_{i+1}/N_i$ is elementary abelian (abelian of prime exponent $r$, for some prime $r$);
--   2. for every $i<j$ (so $N_i<\mathrm{srad}(Q)$), $\mathrm{srad}(Q/N_i)=\mathrm{srad}(Q)/N_i$;
--   3. $j=0$ when $\mathrm{srad}(Q)=1$, and $j=\ell$ when $Q$ is solvable;
--   4. if $j<\ell$, the next factor is $N_{j+1}/N_j=\mathrm{Soc}(Q/\mathrm{srad}(Q))$, and this socle is a direct product of nonabelian simple groups.
--
--   So the group isomorphism algorithm can process the solvable radical one elementary abelian layer at a time and then hand the quotient $Q/\mathrm{srad}(Q)$, which has trivial solvable radical, to the Babai–Codenotti–Qiao algorithm.
--
--   **Formalization Note** The factor $N_{i+1}/N_i$ is the quotient of the subgroup $N_{i+1}$ by $N_i$ viewed inside it; "elementary abelian" is the published `IsElementaryAbelian r`. Clause 4 is stated as: the image of $N_{j+1}$ in $Q/N_j$ is $\mathrm{Soc}(Q/N_j)$, with $N_j=\mathrm{srad}(Q)$.
--
--   Differences from the source:
--
--   - encoding: N_{j+1}/N_j = Soc(Q/srad(Q)) → the image of N_{j+1} in Q/N_j equals Soc(Q/N_j), together with N_j = srad Q; reason: the same subgroup; avoids transporting along the equality N_j = srad Q
--   - encoding: "factors … elementary abelian" → ∃ prime r, `IsElementaryAbelian r` of the quotient group N_{i+1}/(N_i ∩ N_{i+1}); reason: standard meaning (commutative, exponent dividing r)
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), §9.2.1, p.95 (PDF p.99)

import Mathlib
import Definitions.Def_cfsg_elementary_abelian
import Definitions.Def_GroupIsoPoly_charSeries

set_option autoImplicit false

namespace GroupIsoPoly

/-- **§9.2.1 — the series reaches the solvable radical.**

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), §9.2.1, p.95 (PDF p.99): "To see why the series
reaches srad(Q), suppose Ni < srad(Q). Then srad(Q/Ni) = srad(Q)/Ni ≠ 1 … These strict inclusions must
reach srad(Q), giving the index j in (9.3). Thus all factors below Nj are elementary abelian; j = 0
when srad(Q) = 1, and j = ℓ when Q is solvable. If j < ℓ, the next factor is
Nj+1/Nj = Soc(Q/ srad(Q)), a product of nonabelian simple groups."

For every finite group `Q` there is `j ≤ ℓ` with `N_j = srad(Q)` such that
1. for `i < j`, the factor `N_{i+1}/N_i` is elementary abelian (for some prime `r`);
2. for `i < j` (that is, `N_i < srad(Q)`), `srad(Q/N_i) = srad(Q)/N_i`;
3. `j = 0` if `srad(Q) = 1`, and `j = ℓ` if `Q` is solvable;
4. if `j < ℓ`, then `N_{j+1}/N_j = Soc(Q/N_j)` (and `N_j = srad(Q)`), and this socle is a direct
   product of nonabelian simple groups. -/
theorem charSeries_srad (Q : Type*) [Group Q] [Finite Q] :
    ∃ j ≤ seriesLength Q, charSeries Q j = srad Q ∧
      (∀ i < j, ∃ r : ℕ, r.Prime ∧
        IsElementaryAbelian r
          (↥(charSeries Q (i + 1)) ⧸ (charSeries Q i).subgroupOf (charSeries Q (i + 1)))) ∧
      (∀ i < j, srad (Q ⧸ charSeries Q i) = (srad Q).map (QuotientGroup.mk' (charSeries Q i))) ∧
      (srad Q = ⊥ → j = 0) ∧
      (Group.IsSolvable Q → j = seriesLength Q) ∧
      (j < seriesLength Q →
        (charSeries Q (j + 1)).map (QuotientGroup.mk' (charSeries Q j)) = soc (Q ⧸ charSeries Q j) ∧
          IsProdNonabelianSimple (soc (Q ⧸ charSeries Q j))) := by sorry

end GroupIsoPoly
