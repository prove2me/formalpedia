-- Prove2me | Theorems.Thm_OptLocalHamSim_lemma_7
-- name    : OptLocalHamSim.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:36:19.929487+00:00
-- url     : https://prove2.me/theorems/f4f779d8-4639-43a2-8848-922a287719b9
-- title:
--   Lemma 7 — local residual table: $E'(s)=-iK(s)E(s)$, $K(s)=\sum_\lambda c_\lambda e^{i\omega_\lambda s}P_\lambda$ with $A=O(v)$ entries
-- statement:
--   Fix $D\ge1$, $q\ge1$ data qubits per site, $R$, an even order $p\ge2$ and a number $c$ of colors. There are constants $C_{\mathrm{tab}}$, $B$, $\rho$ and $c_*,\omega_*\ge1$ such that for every rectangular block with $v$ sites, every Hamiltonian $H$ satisfying Eq. (1) with local strength at most one, and every coloring of its Pauli summands into $c$ classes with disjoint declared supports, there is a table of $A\le C_{\mathrm{tab}}v$ entries $(x_\lambda,c_\lambda,\omega_\lambda,P_\lambda)$ — an assigned site, a complex coefficient, a real frequency and a Pauli string — with:
--
--   1. at most $B$ entries assigned to each site;
--   2. every non-identity factor of $P_\lambda$ within distance $\rho$ of $x_\lambda$;
--   3. $|c_\lambda|\le c_*$ and $|\omega_\lambda|\le\omega_*$;
--   4. for $E(s):=C(s)^\dagger e^{-iHs}$ (with $C=S_p$) and $K(s):=\sum_{\lambda}c_\lambda e^{i\omega_\lambda s}P_\lambda$: $E(0)=I$, $E'(s)=-iK(s)E(s)$ for all $s$, and
--
--   $$
--   K(s)=\sum_{\lambda=0}^{A-1}\sum_{q=p}^{\infty}c_\lambda\frac{(i\omega_\lambda)^q}{q!}s^qP_\lambda .
--   $$
--
--   The table turns the product-formula residual into a sum of bounded-support Pauli insertions with explicit scalar coefficients, which the LCU of §3.3 encodes.
--
--   Differences from the source:
--   - generalization: p := 2(⌊D/2⌋ + 1) → any even p ≥ 2; reason: the construction and the order conditions hold for every even Suzuki order; the source's p is one
--   - generalization: the greedy coloring → any coloring with disjoint declared supports within a class; reason: the greedy coloring is one such coloring
--   - reading: a classically computable table → the existence of a table; reason: the entries are real and complex numbers, for which Lean has no computability notion; the discrete structure (sites, Pauli supports) is part of the data
--   - reading: The table can be padded to a power-of-two address range using entries with (c_λ, ω_λ, P_λ) = (0, 0, I) → not stated; reason: a remark on how to pad, not a property of the table
--   - encoding: supp(P_λ) lies within a fixed radius of x_λ → every site where P_λ has a non-identity factor is at ℓ¹ distance ≤ ρ from x_λ; reason: the support of a Pauli string
--   - encoding: the expansion (26) → for every s, the series over q ≥ p (reindexed from 0) has sum K(s); reason: the same identity
--   - encoding: H = Σ_{Z⊆Λ} h_Z, each term on a nonempty declared set Z → one matrix h Z for every finite set of sites, with h Z ≠ 0 only on nonempty Z (so h ∅ = 0); reason: several terms on one Z are their sum; no instance changes
--   - encoding: Λ ⊂ ℤ^D a finite rectangular lattice → the box {0,…,L₁−1} × ⋯ × {0,…,L_D−1}; reason: a translate of Λ; the lattice metric is translation invariant
-- source:
--   Shen, Wu, Yao, Yuan, Zhang, Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian Simulation, STOC 2027 submission (held version, sha256 44a9768a…), Lemma 7, eqs. (25)–(26), p.16

import Mathlib
import Definitions.Def_OptLocalHamSim_Site
import Definitions.Def_OptLocalHamSim_IsLocalHam
import Definitions.Def_OptLocalHamSim_Summand
import Definitions.Def_OptLocalHamSim_suzuki
import Definitions.Def_OptLocalHamSim_LCUData

open scoped Matrix

namespace OptLocalHamSim

/-- **Lemma 7 (Local residual table)**, Shen, Wu, Yao, Yuan, Zhang, *Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian
Simulation*, STOC 2027 submission (held version, sha256 44a9768a…), p.16. For E(s) := C(s)†e^{−iH_blk s}, there is a
classically computable table ℛ (entries x_λ, P_λ, c_λ, ω_λ: assigned site, Pauli string, coefficient,
real frequency), with A = O(v) entries, whose associated generator satisfies
K(s) := ∑_{λ=0}^{A−1} c_λ e^{iω_λ s}P_λ, E′(s) = −iK(s)E(s), E(0) = I (25). Each site is assigned a
bounded number of entries, and supp(P_λ) lies within a fixed radius of its assigned site x_λ. There
are model constants c∗, ω∗ ≥ 1 such that |c_λ| ≤ c∗ and |ω_λ| ≤ ω∗. After its vanishing Taylor
coefficients are removed, the generator has the expansion
K(s) = ∑_{λ=0}^{A−1} ∑_{q=p}^{∞} c_λ (iω_λ)^q/q! s^q P_λ (26).

**Formalization Note**
* The block Hamiltonian has local strength at most one (§3 standing assumption, p.14); `C(s) = S_p(s)`
  over the color classes of any proper coloring of its Pauli summands into `c` classes; `p` is any
  even `p ≥ 2` (the paper's `p` is (19)).
* `D ≥ 1` and `q ≥ 1` data qubits per site are the standing assumptions of §1.1, p.4.
* All constants (the `O` in `A = O(v)`, the entries-per-site bound `B`, the radius `ρ`, `c∗`, `ω∗`)
  depend only on `D`, `q`, `R`, `p`, `c`. The radius is measured from `x_λ` to every site at which
  `P_λ` has a non-identity factor.
* "Classically computable" is read as the existence of an explicit table (real coefficients have no
  Lean computability notion). The padding remark of the paper (entries `(0, 0, I)`) is not a property
  of the table and is not stated. -/
theorem lemma_7 (D q : ℕ) (hD : 1 ≤ D) (hq : 1 ≤ q) (R : ℝ) (p : ℕ) (hp : Even p) (hp2 : 2 ≤ p) (c : ℕ) :
    ∃ (Ctab : ℝ) (B ρ : ℕ) (cs ωs : ℝ), 1 ≤ cs ∧ 1 ≤ ωs ∧
      ∀ (L : Fin D → ℕ) (h : Finset (Site L) → Matrix (Dat L q → Bool) (Dat L q → Bool) ℂ),
        IsLocalHam R 1 h →
        ∀ col : Summand h → Fin c, IsProperColoring col →
          ∃ (A : ℕ) (x : Fin A → Site L) (cc : Fin A → ℂ) (ω : Fin A → ℝ)
            (σ : Fin A → Dat L q → Fin 4),
            (A : ℝ) ≤ Ctab * ((∏ j, L j : ℕ) : ℝ) ∧
            (∀ y : Site L, (Finset.univ.filter fun l => x l = y).card ≤ B) ∧
            (∀ l (dq : Dat L q), σ l dq ≠ 0 → l1dist (x l) dq.1 ≤ ρ) ∧
            (∀ l, ‖cc l‖ ≤ cs ∧ |ω l| ≤ ωs) ∧
            SolvesResidual cc ω (fun l => pauliString (σ l)) p
              (fun s => (suzuki (colorHam col) p s)ᴴ * evol (Ham h) s) := by sorry

end OptLocalHamSim
