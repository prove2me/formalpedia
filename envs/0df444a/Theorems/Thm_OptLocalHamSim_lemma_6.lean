-- Prove2me | Theorems.Thm_OptLocalHamSim_lemma_6
-- name    : OptLocalHamSim.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:36:05.257265+00:00
-- url     : https://prove2.me/theorems/00c77e49-c5ad-4f3d-981c-b8605f685800
-- title:
--   Lemma 6 — product-formula error $\|C(s)-e^{-iHs}\|\le C_p\alpha_{\mathrm{com}}|s|^{p+1}\le C'_pv(J|s|)^{p+1}$
-- statement:
--   Fix $D\ge1$, $q\ge1$ data qubits per site, the range $R$, an even order $p\ge2$ and a number $c$ of colors. There are constants $C_p,C'_p\ge0$ such that the following holds for every rectangular block with $v$ sites, every $J>0$, every Hamiltonian $H$ satisfying Eq. (1) with local strength at most $J$, and every coloring of its Pauli summands $F_a$ into $c$ classes with disjoint declared supports within a class. Let $C(s)=S_p(s)$ be the Suzuki formula (21) over the color Hamiltonians. Then for all $s\in\mathbb R$
--
--   $$
--   \bigl\|C(s)-e^{-iHs}\bigr\|\le C_p\,\alpha_{\mathrm{com}}|s|^{p+1}\le C'_p\,v\,(J|s|)^{p+1},
--   $$
--
--   and, if $J\le1$, for every $0<\tau\le1$ and $r\ge1$, with $h=\tau/r$,
--
--   $$
--   \bigl\|C(h)^r-e^{-iH\tau}\bigr\|\le C'_p\,v\,\tau^{p+1}/r^p .
--   $$
--
--   The commutator form makes the error extensive in the block volume, which the parameter balance of Theorem 5 relies on.
--
--   Differences from the source:
--   - generalization: p := 2(⌊D/2⌋ + 1) (eq. (19)) → any even p ≥ 2; reason: the bounds hold for every even Suzuki order with constants depending on p; p = 2(⌊D/2⌋+1) is one such order
--   - generalization: the greedy coloring of the summands into c classes → any coloring into c classes with disjoint declared supports within a class, constants depending on c; reason: the greedy coloring is one such coloring
--   - encoding: the local summands F_a = h_aP_a of Eq. (18) → the nonzero terms of the canonical Pauli expansion of each h_Z, with declared support Z; reason: the expansion of eq. (18)
--   - encoding: ≤ C′_p v|s|^{p+1} (normalized) and C′_p v(J|s|)^{p+1} (local strength at most J) → one bound C′_p v(J|s|)^{p+1} for every J > 0; reason: a Hamiltonian of local strength at most J ≤ 1 also has local strength at most 1, so the normalized bound is the case J = 1
--   - encoding: H = Σ_{Z⊆Λ} h_Z, each term on a nonempty declared set Z → one matrix h Z for every finite set of sites, with h Z ≠ 0 only on nonempty Z (so h ∅ = 0); reason: several terms on one Z are their sum; no instance changes
--   - encoding: Λ ⊂ ℤ^D a finite rectangular lattice → the box {0,…,L₁−1} × ⋯ × {0,…,L_D−1}; reason: a translate of Λ; the lattice metric is translation invariant
-- source:
--   Shen, Wu, Yao, Yuan, Zhang, Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian Simulation, STOC 2027 submission (held version, sha256 44a9768a…), Lemma 6, eqs. (22)–(24), p.15

import Mathlib
import Definitions.Def_OptLocalHamSim_Site
import Definitions.Def_OptLocalHamSim_IsLocalHam
import Definitions.Def_OptLocalHamSim_Summand
import Definitions.Def_OptLocalHamSim_suzuki

open scoped Matrix.Norms.L2Operator

namespace OptLocalHamSim

/-- **Lemma 6 (Local product-formula error; [CST+21, Theorem 6])**, Shen, Wu, Yao, Yuan, Zhang, *Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian
Simulation*, STOC 2027 submission (held version, sha256 44a9768a…), p.15. For the local summands
in Eq. (18), define α_com := ∑_{a₁,…,a_{p+1}} ‖[F_{a_{p+1}}, …, [F_{a₂}, F_{a₁}] …]‖ (22). There are
constants C_p, C′_p, depending only on the fixed local model and p, such that the formula in Eq. (20)
satisfies ‖C(s) − e^{−iH_blk s}‖ ≤ C_p α_com|s|^{p+1} ≤ C′_p v|s|^{p+1} (s ∈ ℝ) (23). For an
unnormalized input of local strength at most J, the last bound is C′_p v(J|s|)^{p+1}. In the
normalized model, the r-step approximation with h := τ/r satisfies
‖C(h)^r − e^{−iH_blk τ}‖ ≤ C′_p vτ^{p+1}/r^p (24).

**Formalization Note**
* The summands are the Pauli expansion of the input terms (`Summand h`), colored by any coloring
  `col` into `c` classes with disjoint declared supports within a class; `C(s)` is the Suzuki formula
  `S_p` (21) over the color Hamiltonians. The constants depend on `D`, `q`, `R`, `p`, `c`.
* The order `p` is any even `p ≥ 2` (the paper fixes `p = 2(⌊D/2⌋+1)`, eq. (19)).
* The bound with `J` covers the normalized one: local strength at most `J ≤ 1` is local strength at
  most `1`. The block is any rectangular lattice; `v = ∏ L_j` is its number of sites.
* `D ≥ 1` and `q ≥ 1` data qubits per site are the standing assumptions of §1.1, p.4.
* (24) is stated under the §3 standing assumption `0 < τ ≤ 1`, for every `r ≥ 1`. -/
theorem lemma_6 (D q : ℕ) (hD : 1 ≤ D) (hq : 1 ≤ q) (R : ℝ) (p : ℕ) (hp : Even p) (hp2 : 2 ≤ p) (c : ℕ) :
    ∃ Cp C'p : ℝ, 0 ≤ Cp ∧ 0 ≤ C'p ∧
      ∀ (L : Fin D → ℕ) (J : ℝ)
        (h : Finset (Site L) → Matrix (Dat L q → Bool) (Dat L q → Bool) ℂ),
        0 < J → IsLocalHam R J h →
        ∀ col : Summand h → Fin c, IsProperColoring col →
          (∀ s : ℝ, ‖suzuki (colorHam col) p s - evol (Ham h) s‖ ≤
            Cp * alphaCom (summandMat (h := h)) p * |s| ^ (p + 1)) ∧
          (∀ s : ℝ, Cp * alphaCom (summandMat (h := h)) p * |s| ^ (p + 1) ≤
            C'p * ((∏ j, L j : ℕ) : ℝ) * (J * |s|) ^ (p + 1)) ∧
          (J ≤ 1 → ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ r : ℕ, 1 ≤ r →
            ‖suzuki (colorHam col) p (τ / r) ^ r - evol (Ham h) τ‖ ≤
              C'p * ((∏ j, L j : ℕ) : ℝ) * τ ^ (p + 1) / (r : ℝ) ^ p) := by sorry

end OptLocalHamSim
