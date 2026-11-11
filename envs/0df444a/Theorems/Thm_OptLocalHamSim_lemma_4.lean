-- Prove2me | Theorems.Thm_OptLocalHamSim_lemma_4
-- name    : OptLocalHamSim.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:35:58.241008+00:00
-- url     : https://prove2.me/theorems/e341388f-de9f-4019-9fcc-92e82f83129d
-- title:
--   Lemma 4 — formal Fact 1: $\|\bar U_\Lambda(t)-\mathcal V(t)\|\le Cne^{-\mu\ell_{\mathrm{buf}}}$ with $O(1)$ computable layers
-- statement:
--   Fix $D\ge1$, $q\ge1$ data qubits per site and the range $R$. There are constants $C,\mu>0$, an integer $\ell_0$, a bound $L_H$ and a computable map from (side lengths of $\Lambda$, $\ell_{\mathrm{buf}}$) to layers $\mathcal B_1,\dots,\mathcal B_{L}$ of signed regions such that, whenever $\ell_{\mathrm{buf}}\ge\ell_0$ and every side of $\Lambda$ is at least $C\ell_{\mathrm{buf}}$:
--
--   1. there are $L\le L_H$ layers;
--   2. every region lies in $\Lambda$ and has side lengths in $[\ell_{\mathrm{buf}},C\ell_{\mathrm{buf}}]$;
--   3. the regions of one layer are pairwise disjoint;
--   4. $\sum_a\sum_{Y\in\mathcal B_a}|Y|\le Cn$;
--   5. for every Hamiltonian $\bar H$ satisfying Eq. (1) with local strength at most one and every $|t|\le1$,
--
--   $$
--   \bigl\|\bar U_\Lambda(t)-\mathcal V(t)\bigr\|\le Cn\,e^{-\mu\ell_{\mathrm{buf}}},\qquad \mathcal V(t):=\mathcal V_{L}(t)\cdots\mathcal V_1(t),\quad \mathcal V_a(t):=\prod_{Y\in\mathcal B_a}\bar U_Y(\sigma_{a,Y}t).
--   $$
--
--   Here $n$ is the number of qubits. The lemma replaces each normalized time interval by a constant number of layers of block evolutions of side $\Theta(\ell_{\mathrm{buf}})$, which Theorem 5 then simulates.
--
--   **Formalization Note** "The regions, signs, and layer order can be computed classically from the lattice and $\ell_{\mathrm{buf}}$" is a `Computable` function of the list of side lengths and $\ell_{\mathrm{buf}}$, whose single output serves every such Hamiltonian and every $|t|\le1$.
--
--   Differences from the source:
--   - reading: The regions, signs, and layer order can be computed classically from the lattice and ℓ_buf → the layers are the output of a Computable function of (side lengths, ℓ_buf), and that one output satisfies the bound for every normalized h and every |t| ≤ 1; reason: the regions depend only on the lattice and ℓ_buf by the source's sentence; this is the stronger reading
--   - encoding: regions Y ∈ B_a with signs σ_{a,Y} → lists of (corner, sides) with a Boolean sign (true = +1); reason: classical data for the same boxes
--   - encoding: the normalized local model H̄ = sgn(T)H/J → any h with IsLocalHam R 1 h; Ū_Y(t) = e^{−iH_Y t} for its terms; reason: H̄ has local strength at most one and range R, and every such Hamiltonian is a normalized model (take T > 0, J = 1)
--   - encoding: L_H = O(1) layers, ∑|Y| = O(n) → length ≤ L_H for a constant L_H, ∑|Y| ≤ C·n; reason: explicit constants fixed before Λ
--   - encoding: H = Σ_{Z⊆Λ} h_Z, each term on a nonempty declared set Z → one matrix h Z for every finite set of sites, with h Z ≠ 0 only on nonempty Z (so h ∅ = 0); reason: several terms on one Z are their sum; no instance changes
--   - encoding: Λ ⊂ ℤ^D a finite rectangular lattice → the box {0,…,L₁−1} × ⋯ × {0,…,L_D−1}; reason: a translate of Λ; the lattice metric is translation invariant
--   - encoding: an integer ℓ₀ → ℓ₀ : ℕ (and ℓ_buf : ℕ); reason: ℓ_buf is a natural length, so a negative ℓ₀ can be replaced by 0 without changing any instance
-- source:
--   Shen, Wu, Yao, Yuan, Zhang, Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian Simulation, STOC 2027 submission (held version, sha256 44a9768a…), Lemma 4, eqs. (8)–(9), p.11

import Mathlib
import Definitions.Def_OptLocalHamSim_Site
import Definitions.Def_OptLocalHamSim_IsLocalHam
import Definitions.Def_OptLocalHamSim_boxOf

open scoped Matrix.Norms.L2Operator

namespace OptLocalHamSim

/-- **Lemma 4 (Formal form of Fact 1; [HHKL23, Lemma 6 and proof of Theorem 1])**, Shen, Wu, Yao, Yuan, Zhang, *Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian
Simulation*, STOC 2027 submission (held version, sha256 44a9768a…), p.11. For the
normalized local model, there are constants C, µ > 0 and an integer ℓ₀ such that the following holds.
Suppose ℓ_buf ≥ ℓ₀ and every side of Λ is at least Cℓ_buf. For |t| ≤ 1, there are L_H = O(1) layers
B_1, …, B_{L_H} of disjoint regions with signs σ_{a,Y} ∈ {−1, 1} for which
𝒱(t) := 𝒱_{L_H}(t) ⋯ 𝒱_1(t), 𝒱_a(t) := ∏_{Y∈B_a} Ū_Y(σ_{a,Y}t) (8) obeys
‖Ū_Λ(t) − 𝒱(t)‖ ≤ Cne^{−µℓ_buf} (9). Every region Y has side lengths in [ℓ_buf, Cℓ_buf], and
∑_a ∑_{Y∈B_a} |Y| = O(n). The regions, signs, and layer order can be computed classically from the
lattice and ℓ_buf.

**Formalization Note**
* "Normalized local model": any `h` with `IsLocalHam R 1 h` (local strength ≤ 1); `Ū_Y(t)` is
  `evol (HamOn h Y) t`. The constants `C`, `µ`, `ℓ₀` and the layer bound `L_H` depend only on
  `D`, `q`, `R`. The paper's single constant `C` is used for all three bounds, as printed.
* The layers are the output of one `Computable` function `layersOf` of (the list of side lengths,
  `ℓ_buf`); a layer is a list of regions, each a box `(corner, sides)` with a sign (`true` = +1).
  The same output serves every `h` and every `|t| ≤ 1` (reading of "computed classically from the
  lattice and ℓ_buf").
* Within a layer the regions are pairwise disjoint, so the factors of `𝒱_a` commute.
* `D ≥ 1` and `q ≥ 1` data qubits per site are the standing assumptions of §1.1, p.4.
* `n = q·∏ L_j` is the number of qubits; `|Y|` is the number of sites of `Y`. -/
theorem lemma_4 (D q : ℕ) (hD : 1 ≤ D) (hq : 1 ≤ q) (R : ℝ) :
    ∃ (C μ : ℝ) (ℓ₀ LH : ℕ), 0 < C ∧ 0 < μ ∧
      ∃ layersOf : List ℕ × ℕ → List (List ((List ℕ × List ℕ) × Bool)), Computable layersOf ∧
        ∀ (L : Fin D → ℕ) (ℓbuf : ℕ), ℓ₀ ≤ ℓbuf → (∀ j, C * (ℓbuf : ℝ) ≤ (L j : ℝ)) →
          (layersOf (List.ofFn L, ℓbuf)).length ≤ LH ∧
          (∀ layer ∈ layersOf (List.ofFn L, ℓbuf), ∀ Y ∈ layer,
            BoxFits L (ℓbuf : ℝ) (C * ℓbuf) Y.1) ∧
          (∀ layer ∈ layersOf (List.ofFn L, ℓbuf),
            layer.Pairwise fun Y Y' => Disjoint (boxOf L Y.1) (boxOf L Y'.1)) ∧
          ((((layersOf (List.ofFn L, ℓbuf)).map fun layer =>
              (layer.map fun Y => (boxOf L Y.1).card).sum).sum : ℕ) : ℝ) ≤
            C * (numQubits L q : ℝ) ∧
          ∀ h : Finset (Site L) → Matrix (Dat L q → Bool) (Dat L q → Bool) ℂ, IsLocalHam R 1 h →
            ∀ t : ℝ, |t| ≤ 1 →
              ‖evol (Ham h) t - layersProduct L h (layersOf (List.ofFn L, ℓbuf)) t‖ ≤
                C * (numQubits L q : ℝ) * Real.exp (-(μ * ℓbuf)) := by sorry

end OptLocalHamSim
