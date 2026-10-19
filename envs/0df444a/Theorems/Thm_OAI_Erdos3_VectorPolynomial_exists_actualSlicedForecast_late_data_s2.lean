-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_actualSlicedForecast_late_data_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_actualSlicedForecast_late_data_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T05:08:46.310057+00:00
-- url     : https://prove2.me/theorems/29980c43-25ca-4410-b1cf-6463dd667286
-- title:
--   An admissible sliced path built with early numerics admits forecast data at the late numerics' parameters
-- statement:
--   All named objects below are defined by OpenAI. Let $m$ be a natural number, $G$ a finite type, and for $j < m$ let $I_j$, $J_j$, $E^{\mathrm{out}}_j$ be finite types and $n_j$ natural numbers; let $B_a$ be finite types indexed by `LayerSamplerAxis I n`. For each $j$ let $U_j$ be a real subspace of $\mathbb{R}^{J_j}$ and $b_j$ a basis, indexed by $\{0,\dots,n_j-1\}$, of the orthogonal complement of the Euclidean copy of $U_j$. Let $R_j, \sigma_j$ be reals with proofs `hR`, `hσ` that $R_j > 0$ and $\sigma_j > 0$, and $S$ a `LayerSamplerScale B U b R σ`. Let $X$ be a finite type with decidable equality, $D_{\mathrm{mod}}, L_{\mathrm{rank}}$ natural numbers, `spatial`, `kernel`, `block` the embeddings into $G$ and into the $B_{(j,a)}$ for the allocated degree-active axes, $T_{\mathrm{sp}}$ a finite type, `spatialEquiv` an equivalence $G \simeq X \sqcup (X \sqcup T_{\mathrm{sp}})$, reals $W_{\mathrm{sp}}, L_{\mathrm{sp}}, \tau, \delta_{\mathrm{slice}}$, `physicalN : X → ℕ`, a finite type $A$ and a map `selected` from $A$ to the pairs $(j, i)$ with $i < n_j$.
--
--   Let `s` be an `ActualFixedSpatialForecastSetup B U b S Dmod selected τ δslice`, and let `qEarly`, `qLate` be two `ActualFixedSpatialSlicedForecastNumerics s` (numerical parameter packages, with fields including $\delta$, `Hchild`, $v$, `Ptail`, `Pnative`, `massLog`, `capLog`, $E$). Let $o_j$ be an orthonormal basis (indexed by $I_j$) of the Euclidean copy of $U_j$; `bW j` a $\mathbb{Z}$-basis, indexed by $E^{\mathrm{out}}_j$, of the `latticeSection` of the standard lattice $\mathbb{Z}^{J_j}$ in that subspace; `hb` a proof that for each $j$ the $\mathbb{Z}$-span of the range of $b_j$ is the `projectedIntegerLattice` of the Euclidean copy of $U_j$; `originalpoly j` vector polynomials in the variables $X$ with values in $\mathbb{R}^{J_j}$, with `hmem` a proof that all their coefficients lie in $U_j$. Let `member` be an `ActualFixedSpatialSlicedAdmissiblePath s qEarly` (for the data above). Assume that `qEarly` and `qLate` agree in the fields $\delta$, `Hchild`, $v$ and `Ptail`.
--
--   Then there exists `data`, an `ActualForecastData physicalN originalpoly qLate.Pnative qLate.massLog qLate.capLog qLate.E` (a structure of OpenAI consisting of a target function on `integerBox physicalN`, center constants, a finite family of complex coefficients and normalized polynomial twists with period, cover and Lipschitz caps $e^{3P_{\mathrm{native}}+3}$, with target bounded by $e^{\mathrm{capLog}}$, total coefficient mass at most $e^{\mathrm{massLog}}$, and the target approximated within $e^{-E}$ by the twist combination for `originalpoly`), such that:
--   - `data.target = member.slice.target selected s.hBactive o bW hb originalpoly hmem s.κ`;
--   - `data.centerConstant` $= (j \mapsto$ `(member.slice.path.center j).val`$)$;
--   - for every family of vector polynomials `poly j` with all coefficients in $U_j$ (proof `hm`) and every $u : X \to \mathbb{Z}$,
--   $$\Bigl\|\texttt{member.slice.targetAt selected s.hBactive o bW hb poly hm s.κ}\ u - \sum_t \texttt{data.coefficient}\ t \cdot (\texttt{data.twists}\ t).\texttt{eval}\ \mathrm{physicalN}\ \bigl(j \mapsto \texttt{subtractConstant}\ (\texttt{data.centerConstant}\ j)\ (\mathrm{poly}\ j)\bigr)\ u\Bigr\| \le e^{-\texttt{qLate.E}}.$$
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_actualSlicedForecast_late_data_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_actualSlicedForecast_late_data` (in `lean/OAI/Combinatorics/Progressions/Sampling/ActualSlicedForecastLateData.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B301` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ActualSlicedForecastLateData.lean (declaration OAI.Erdos3.VectorPolynomial.exists_actualSlicedForecast_late_data)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B301

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (qEarly qLate : ActualFixedSpatialSlicedForecastNumerics s)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)

variable (member : ActualFixedSpatialSlicedAdmissiblePath
  (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
  (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qEarly)
variable (hδ : qEarly.δ = qLate.δ) (hH : qEarly.Hchild = qLate.Hchild)
variable (hv : qEarly.v = qLate.v) (hPtail : qEarly.Ptail = qLate.Ptail)

include hδ hH hv hPtail in

theorem exists_actualSlicedForecast_late_data_s2 :
    ∃ data : ActualForecastData physicalN originalpoly qLate.Pnative qLate.massLog qLate.capLog qLate.E,
      data.target = member.slice.target selected s.hBactive o bW hb originalpoly hmem s.κ ∧
      data.centerConstant = (fun j => (member.slice.path.center j).val) ∧
      ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (hm : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
        ‖member.slice.targetAt selected s.hBactive o bW hb poly hm s.κ u -
          ∑ t, data.coefficient t * (data.twists t).eval physicalN
            (fun j => subtractConstant (data.centerConstant j) (poly j)) u‖ ≤ Real.exp (-qLate.E) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
