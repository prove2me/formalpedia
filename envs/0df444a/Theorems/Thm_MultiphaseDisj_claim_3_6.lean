-- Prove2me | Theorems.Thm_MultiphaseDisj_claim_3_6
-- name    : MultiphaseDisj.claim_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:29:33.798031+00:00
-- url     : https://prove2.me/theorems/02004201-ed37-406a-b4cd-9c5587c6a7ae
-- title:
--   Claim 3.6 — direct sum over the query sets
-- statement:
--   Let $\vec S=(S_1,\dots,S_m)$ and $Y$ be random variables with an arbitrary joint law on a finite set, and let the query index $Q$ be uniform on $[m]$ and independent of $(\vec S,Y)$. For any random variables $V$ and $W$ that are functions of $(\vec S,Y)$,
--   $$
--   I\big(S_Q;\,W\ \big|\ V,Q,S_{<Q}\big)=\frac1m\,I\big(\vec S;\,W\ \big|\ V\big),
--   $$
--   where $S_{<Q}=(S_1,\dots,S_{Q-1})$ and information is measured in bits.
--
--   In the paper $Y=(X,R_{\mathrm{Bob}})$. The identity is how the analysis divides the information carried by Merlin's long message $U$, which is shared by all $m=n$ query sets, by $m$.
--
--   Differences from the source:
--   - generalization: V, W functions of (S⃗, X, R_Bob) under the hard distribution and R_Bob → any finite joint law of (S⃗, Y), with S_j in any finite type and V, W functions of (S⃗, Y); reason: the proof (p.20) uses only that Q is uniform and independent of (S⃗, X, R_Bob); take Y = (X, R_Bob)
--   - encoding: S_{<Q} = (S₁, …, S_{Q−1}) → the tuple with entries S_j for j < Q and empty entries from Q on; reason: with Q in the conditioning it carries the same information
--   - encoding: H, I, H∞ and log with base 2 (§2.2) → entropy, mutual information and min-entropy in bits on finite sample spaces with real point masses; reason: same quantities
-- source:
--   Ko, Unconditional Boolean Dynamic Lower Bounds from Disjointness, arXiv:2610.10904 (held version, sha256 ba26649b…), Claim 3.6, p.20

import Mathlib
import Definitions.Def_MultiphaseDisj_HardDist

set_option autoImplicit false

namespace MultiphaseDisj

/-- **Claim 3.6 (Direct sum)** (Ko, *Unconditional Boolean Dynamic Lower Bounds from Disjointness*, arXiv:2610.10904, held
version sha256 ba26649b…, Claim 3.6, p.20). For any random variables `V` and `W`
that are functions of `(S⃗, X, R_Bob)`,
`I(S_Q; W | V, Q, S_{<Q}) = (1/m) · I(S⃗; W | V)`.

**Formalization Note** Stated for any finite joint law `μ` of `(S⃗, Y)` with
`S⃗ = (S_1, …, S_m)` taking values in any finite type `σ` (in the paper `Y = (X, R_Bob)`), and
the query index `Q` uniform on `[m]` and independent of `(S⃗, Y)`: the proof (p.20) uses only
that `Q` is uniform and independent. `S_{<Q}` is `prefixBefore S⃗ Q`; information is in bits. -/
theorem claim_3_6 {m : ℕ} {σ Y α β : Type*} [Fintype σ] [Fintype Y]
    (μ : (Fin m → σ) × Y → ℝ) (hμ : IsDist μ)
    (V : (Fin m → σ) × Y → α) (W : (Fin m → σ) × Y → β) :
    condMI (fun ω : ((Fin m → σ) × Y) × Fin m => μ ω.1 * (1 / (m : ℝ)))
        (fun ω => ω.1.1 ω.2) (fun ω => W ω.1)
        (fun ω => (V ω.1, ω.2, prefixBefore ω.1.1 ω.2)) =
      (1 / (m : ℝ)) * condMI μ Prod.fst W V := by sorry

end MultiphaseDisj
