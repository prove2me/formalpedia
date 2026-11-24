-- Prove2me | Theorems.Thm_IntConeFPT_section_3_6_nstar_bound
-- name    : IntConeFPT.section_3_6_nstar_bound
-- status  : Proved
-- author  : @ohnesorgefelix
-- created : 2026-11-24T11:16:36.889789+00:00
-- url     : https://prove2.me/theorems/797de649-3693-4a16-a90c-cb7f0eacf5e3
-- title:
--   §3.6 — Denominator-cleared integral description, homogenized instance $\hat I$, and encoding bound for $N_\star$
-- statement:
--   Let $I$ be a valid instance of (♣) ($d \ge 1$, $\tau \ge 1$, each $P^{(t)}$ bounded, each $f^{(t)}$ convex on $P_x^{(t)}$), and let $M \ge 1$ be an integer coordinate bound. Write $|I|$ for the binary encoding length of $I$, $\operatorname{enc}(n)$ for the binary encoding of $n \in \mathbb{N}$, $s := \tau 2^d$, $U := U(I, M) \ge 1$ for the cleared-system coefficient bound (`coeffBoundU`), $\widehat{I}$ for the homogenized instance (`homInstance`), and $N_\star := s(s+1)s!\, H^s$ with $H = (sk+1)!\, U^{sk+1}$ as in (3.4). Then:
--
--   1. The denominator-cleared system $D = \operatorname{clearIntDesc}(I)$ is an exact integral description of $(Q, \mathcal{A}, (P^{(t)})_t)$, satisfies $U \ge 1$ and the coefficient bound `BoundedBy` for $(M, U)$, and its homogeneous aggregate system characterizes $\widehat{Q}$ and $\widehat{\mathcal{A}}$:
--   $$
--   W y_{\mathrm{agg}} \le 0 \iff \sum_{t=1}^{\tau} (y^{(t)}, v^{(t)}) \in \widehat{Q} \;\wedge\; y_{\mathrm{agg}} \in \widehat{\mathcal{A}}.
--   $$
--   2. The homogenized instance $\widehat{I}$ is valid and satisfies $|\widehat{I}| \le |I|$.
--   3. Every valid instance satisfies $1 \le |I|$, $d \le |I|$, $k \le |I|$, and $\tau \le |I|$, and the binary encoding length of $N_\star$ obeys
--   $$
--   |\operatorname{enc}(N_\star)| \le 64\, (\tau 2^d)^3 \bigl(|I| + |\operatorname{enc}(M)|\bigr)^2.
--   $$
--
--   This formalizes the denominator-clearing construction, the homogenized instance size property, and the encoding-length bound $\operatorname{enc}(N_\star) = s^{O(1)} |I|^{O(1)} = \tau^{O(1)} 2^{O(d)} |I|^{O(1)}$ from Section 3.6 (pp. 17–18) needed to apply Lemma 15 and bound the input lengths of the two calls to Proposition 14.
--
--   **Formalization Note** Encoding lengths are measured as `(encInstance I).length` and `(encNat ·).length` over the four-symbol alphabet `Sym = Fin 4`.
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint, sha256 9e28aed8…bc08a), §3.6, pp.17–18, eq. (3.4) and Proof of Theorem 1

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Instance
import Definitions.Def_IntConeFPT_Problem
import Definitions.Def_IntConeFPT_Residue
import Definitions.Def_IntConeFPT_Formulation
import Definitions.Def_IntConeFPT_Homogenized

open OnlineCRS.Combine

namespace IntConeFPT

/-- **Section 3.6: integral description, homogenized instance, and encoding bound for `N⋆`.**
Jansen–Ohnesorge–Schumacher, *A Constructive FPT Algorithm for Integer Cone Optimization with
Convex Costs*, arXiv:2609.31328 (preprint), §3.6, pp.17–18: clearing denominators in `Q`, `A`, and
`P^(t)` yields an integral description bounded by `U = coeffBoundU I M ≥ 1`, its homogeneous
left-hand sides characterize `Q̂` and `Â`, the homogenized instance `homInstance I` is valid with
no larger encoding length than `I`, and the multiplicity bound `N⋆` of (3.4) has encoding length
`enc(N⋆) = s^{O(1)} |I|^{O(1)} = τ^{O(1)} 2^{O(d)} |I|^{O(1)}`. -/
theorem section_3_6_nstar_bound (I : Instance) (hI : I.Valid) (M : ℕ) (hM : 1 ≤ M) :
    (clearIntDesc I).Describes ∧
    (∀ Y : Fin I.τ → Pt I.d I.k,
      (∀ i, (clearIntDesc I).aggLHS Y i ≤ 0) ↔
        ((∑ t, ((Y t).1, (Y t).2.1)) ∈ I.Qhat ∧ Y ∈ I.Ahat)) ∧
    1 ≤ coeffBoundU I M ∧
    (clearIntDesc I).BoundedBy M (coeffBoundU I M) ∧
    (homInstance I).Valid ∧
    (encInstance (homInstance I)).length ≤ (encInstance I).length ∧
    1 ≤ (encInstance I).length ∧
    I.d ≤ (encInstance I).length ∧
    I.k ≤ (encInstance I).length ∧
    I.τ ≤ (encInstance I).length ∧
    (encNat (Nstar I.τ I.d I.k (coeffBoundU I M))).length ≤
      64 * (I.τ * 2 ^ I.d) ^ 3 * ((encInstance I).length + (encNat M).length) ^ 2 := by sorry

end IntConeFPT
