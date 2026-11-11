-- Prove2me | Theorems.Thm_LindbladShallow_lemma_A_4
-- name    : LindbladShallow.lemma_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:21:00.383026+00:00
-- url     : https://prove2.me/theorems/08e8471a-7fd8-45b9-ae19-16df9331c3e3
-- title:
--   Lemma A.4 — physical channel accuracy
-- statement:
--   Let $m_{\mathrm{tot}}\ge0$ be an integer, $h\ge0$ and $T=m_{\mathrm{tot}}h$. For a valid input, the forward collision circuit in the prescribed term order, with an independent fresh bath for each jump label (all baths in vacuum, traced out at the end), induces a CPTP channel $\Phi$, equal to $\Phi_h^{m_{\mathrm{tot}}}$ for the one-period fresh-bath channel $\Phi_h$. If $h\lambda\le1$,
--   $$\big\|\Phi-e^{T\mathcal L}\big\|_\diamond\le\tfrac12n\lambda^2Th\le C_{\mathrm{col}}n\lambda^2Th,\qquad C_{\mathrm{col}}=8(\kappa+1).$$
--
--   This is the collision-discretization error, the first term ($\epsilon/16$) of the error budget of Theorem 2.1.
--
--   Differences from the source:
--   - reading: the channel induced by the forward fresh-label circuit → Tr_baths of collU over m_tot periods (every retained term active, no restriction, bath (e, m) per jump occurrence) applied to E₀, with the identity Φ = Φ_h^{m_tot} stated as an extra conjunct; reason: the source asserts this identity (p.12–13: "T/h forward periods induce Φ_h^{T/h}"; proof of Lemma A.4), so stating it adds no claim beyond the page
--   - encoding: T = m_tot h (a time of the lemma) → the input's own rational T and ϵ are not used; λ, n and ℒ are the input's; reason: the lemma is stated for an arbitrary number of periods
--   - encoding: ‖Φ‖_⋄ = sup_{r≥1} sup_{Z≠0} ‖(Φ⊗I_r)(Z)‖₁/‖Z‖₁ → dnorm: an ℝ≥0∞ supremum over every r ≥ 1 and every nonzero complex Z, reference factor first (id_r ⊗ Φ), trace norm QAlgorithms.traceNorm; reason: Lean convention; reordering tensor factors changes no value and the ℝ≥0∞ supremum has no junk value
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), Lemma A.4, p.60, Eq. (63)

import Mathlib
import Definitions.Def_LindbladShallow_gen
import Definitions.Def_LindbladShallow_lam
import Definitions.Def_LindbladShallow_collision

open scoped Matrix ComplexOrder ENNReal

namespace LindbladShallow

/-- **Lemma A.4** (Physical channel accuracy; arXiv:2610.05362, held version sha256 8f4637ef…,
p.60). Let `m_tot ≥ 0` be an integer, `h ≥ 0` and `T = m_tot h`. The forward collision circuit, in
the prescribed term order with an independent fresh bath for each jump label, induces a CPTP
channel. If `hλ ≤ 1`, its diamond distance from `e^{Tℒ}` is at most
`½ nλ²Th ≤ C_col nλ²Th`, `C_col = 8(κ + 1)` (63).

**Formalization Note** The forward fresh-label circuit is `collU` over `m_tot` periods with every
(retained) term active and no spatial restriction: occurrence `(e, m)` of a dissipative term acts on
its own bath `(e, m)`, all baths start in vacuum (`E₀`) and are traced out at the end of the circuit.
Its channel `Φ` is stated to equal `Φ_h^{m_tot}`, the `m_tot`-fold composition of the one-period
fresh-bath channel (p.12–13: "T/h forward periods induce Φ_h^{T/h}"; the proof of Lemma A.4).
`λ` is the instance's strength of Eq. (2); `T` here is `m_tot h`, not the input's time. -/
theorem lemma_A_4 {P : Params} (I : Instance P) (hI : I.Valid) (mtot : ℕ) (h : ℝ) (hh : 0 ≤ h)
    (hlam : h * lam I ≤ 1) :
    let Φ : QAlgorithms.Superop (Sys I) (Sys I) :=
      isoChannel (collU I mtot h (fun _ => True) Set.univ * E0 I mtot)
    Φ = (periodChannel I h)^[mtot] ∧
      QAlgorithms.IsChannel Φ ∧
      dnorm (Φ - ⇑(supExp ((mtot : ℝ) * h) (gen I))) ≤
        ENNReal.ofReal ((1 / 2) * I.n * lam I ^ 2 * ((mtot : ℝ) * h) * h) ∧
      (1 / 2) * (I.n : ℝ) * lam I ^ 2 * ((mtot : ℝ) * h) * h ≤
        (8 * ((P.κ : ℝ) + 1)) * I.n * lam I ^ 2 * ((mtot : ℝ) * h) * h := by sorry

end LindbladShallow
