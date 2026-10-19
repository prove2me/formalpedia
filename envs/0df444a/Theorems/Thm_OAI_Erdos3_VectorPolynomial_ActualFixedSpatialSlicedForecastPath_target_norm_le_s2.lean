-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_target_norm_le_s2
-- name    : OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.target_norm_le_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T05:28:53.392791+00:00
-- url     : https://prove2.me/theorems/bf251374-a511-41e3-8dcd-8e156341c1cf
-- title:
--   A norm bound for the target of a sliced forecast path
-- statement:
--   Fix: a natural number $m$; a finite type $G$; finite types $I_j$ ($j \in \mathrm{Fin}\,m$) and $n : \mathrm{Fin}\,m \to \mathbb N$; finite types $B_a$ for $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \le \mathbb R^{J_j}$ and bases $b_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`; reals $R_j, \sigma_j$, a `LayerSamplerScale` $S$ for $(B, U, b, R, \sigma)$ over $G$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities), and proofs $hR$, $h\sigma$ that $R_j > 0$ and $\sigma_j > 0$; a finite type $X$ with decidable equality; finite types $E_j$ (`Eout`); natural numbers $D_{\mathrm{mod}}$ and $L$; embeddings $\mathrm{spatial} : \mathrm{Fin}\,L \hookrightarrow G$, $\mathrm{kernel}_j : \mathrm{Fin}\,L \times \mathrm{Fin}(j+1) \hookrightarrow G$, and $\mathrm{block}_{j,a} : \mathrm{Fin}\,L \hookrightarrow B_{\langle j, a\rangle}$ for every axis $a$ of layer $j$ that is not short (`AllocatedDegreeActiveAxis short j`, where $\mathrm{short}$ is the predicate `allocatedShortAxis U b S.value`, true exactly of the axes $\langle j, \mathrm{inr}\ i\rangle$ with `basisAxisScale (b j) i` $\le S.\mathrm{value}^{j+1}$); a finite type $T$ and an equivalence $G \simeq X \oplus (X \oplus T)$; reals $W_{\mathrm{sp}}, L_{\mathrm{sp}}$; $N : X \to \mathbb N$ (`physicalN`); reals $\tau, \delta_{\mathrm{slice}}$; a finite type $A$ and $\mathrm{selected} : A \to \Sigma_j\, \mathrm{Fin}(n_j)$. Let $s$ be an `ActualFixedSpatialForecastSetup B U b S Dmod selected τ δslice` (over $X$ and $E$; a structure bundling inequalities and real parameters, among them $s.P$, $s.P_{\mathrm{bad}}$, $s.P_{\mathrm{pres}}$, $s.P_{\mathrm{cap}}$, $s.\kappa$, a proof `s.hδslice` of $\delta_{\mathrm{slice}} > 0$ and a proof `s.hBactive` that $|B_a| \ge 4$ for every axis $a$ that is not short), and `slice` an `ActualFixedSpatialSlicedForecastPath` over these data with parameters $(P, P_{\mathrm{bad}}, P_{\mathrm{pres}}) = (s.P, s.P_{\mathrm{bad}}, s.P_{\mathrm{pres}})$ (a structure bundling an `ActualFixedSpatialForecastPath` `slice.path` with a step, kernel data, and principal lengths, steps and starts on `PrincipalTupleIndex B (layerSamplerDegree I n)`). For $a \in A$ with $\mathrm{selected}(a) = (j_a, i_a)$ write $a^* = \langle j_a, \mathrm{inr}\ i_a\rangle$ and $H =$ `allocatedPrincipalSides B U b S`.
--
--   Let $\delta > 0$ be real and $H_{\mathrm{child}}$ a natural number such that for every $a \in A$, either $H_{(a^*, b_0, v_0)} < H_{\mathrm{child}}$ for some $b_0, v_0$, or [$\delta\, H_{(a^*, i, v)} \le$ `slice.principalLength` $(a^*, i, v)$ and `slice.principalStep` $(a^*, i, v) > 0$ for all $i, v$]. Let $P_{\mathrm{tail}}, C_{\mathrm{tail}}$ be reals with $P_{\mathrm{tail}} \ge 1$, $s.P_{\mathrm{cap}} \le P_{\mathrm{tail}}$, `slice.principalStep` $(a^*, i, v) \le P_{\mathrm{tail}}$ for all $a, i, v$, $C_{\mathrm{tail}} \ge 0$, and for every $a \in A$, with $\mathrm{degree} = j_a + 1$, $\mathrm{denom} =$ `inactiveDenominator (principalProfileSize (R j_a) |layerIntegerPrincipalSlots B j_a i_a|)` (here `inactiveDenominator γ` $= \max(1, \lceil 1/\gamma \rceil)$ and `principalProfileSize R b` $= R/(8(b+1))$), $\mathrm{torus} =$ `blockTorusFactor 0 degree |B a*| 1`, $V = \mathrm{torus} \cdot \mathrm{denom} \cdot 2^{\mathrm{degree}} / \delta^{\mathrm{degree}}$ and $\mathrm{cutoff} = \max(\mathrm{allocatedSlicedGridHeightCutoff}(B, j_a, i_a, \lceil 1/\delta \rceil),\ \mathrm{denom} \cdot 2^{\mathrm{degree}} H_{\mathrm{child}}^{\mathrm{degree}} + 2\,\mathrm{denom})$, we have $\max(\mathrm{cutoff}, \mathrm{uniformSpectrumAbsoluteCap}(j_a, 1, \mathrm{degree}, P_{\mathrm{tail}}, V, V)) \le C_{\mathrm{tail}}$. Let $o_j$ be orthonormal bases of `euclideanSubspace (U j)` indexed by $I_j$; $bW_j$ $\mathbb Z$-bases, indexed by $E_j$, of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`; $hb$ the statement that the $\mathbb Z$-span of $b_j$ is `projectedIntegerLattice (euclideanSubspace (U j))`; $\mathrm{originalpoly}_j$ vector polynomials on $X$ with values in $\mathbb R^{J_j}$ whose coefficients lie in $U_j$ (hypothesis $hmem$); and $u$ a point of `integerBox physicalN`.
--
--   Put $\mathrm{cap} =$ `fixedSpatialOriginalForecastCap B (slice.slicedBlockEquiv true) s.hδslice` (a nonnegative real defined by OpenAI) and
--   $$C_{\mathrm{decay}} = \Bigl(R_{\mathrm{bad}} \prod_{q \in \mathrm{primes}} q^{\mathrm{prescribed}(q)}\Bigr)^{\mathrm{modularRankDecayExponent}(m,\ \mathrm{modularForecastRankConstant}(m, D_{\mathrm{mod}})) \cdot \mathrm{modularRankChargeFactor}(m)},$$
--   with $R_{\mathrm{bad}}$, $\mathrm{primes}$, $\mathrm{prescribed}$ the fields of `slice.path`, `modularForecastRankConstant s D` $= (D+2)(2^s s!)2^s$, `modularRankDecayExponent s C` $= C/(2^s s!)/2^s$ and `modularRankChargeFactor s` $= 4s(2^s s!)$. Then the complex number `slice.target selected s.hBactive o bW hb originalpoly hmem s.κ u` (defined by OpenAI as $s.\kappa$ times a `forecastLawDensityPhysicalTarget` built from the slice's principal law, density and path data) satisfies
--   $$\|\mathrm{slice.target}(\dots, u)\| \le s.\kappa \cdot \mathrm{cap} \cdot C_{\mathrm{tail}}^{|A|} \cdot (1 + C_{\mathrm{decay}}).$$
--
--   Lean: `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.target_norm_le_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.target_norm_le` (in `lean/OAI/Combinatorics/Progressions/Sampling/ActualFixedSpatialSlicedInactiveGridCap.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B245` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ActualFixedSpatialSlicedInactiveGridCap.lean (declaration OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.target_norm_le)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B245

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

namespace ActualFixedSpatialSlicedForecastPath

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice s.P s.Pbad s.Ppres)

theorem target_norm_le_s2
    (δ : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U b S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ i v, δ * allocatedPrincipalSides B U b S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ ≤
        (slice.principalLength ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ : ℝ)) ∧
       (∀ i v, 0 < slice.principalStep ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩)))
    (Ptail Ctail : ℝ) (hPtail : 1 ≤ Ptail)
    (hsPtail : s.Pcap ≤ Ptail)
    (hstrideTail : ∀ a i v,
      (slice.principalStep ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ : ℝ) ≤ Ptail)
    (hCtail : 0 ≤ Ctail)
    (htailactual : ∀ a,
      let degree := (selected a).1.val + 1
      let denom := inactiveDenominator (principalProfileSize (R (selected a).1)
        (Finset.card (layerIntegerPrincipalSlots (G := G) B (selected a).1 (selected a).2)))
      let torus := blockTorusFactor (Fintype.card Empty) degree
        (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) 1
      let V := (torus : ℝ) * ((denom : ℝ) * 2 ^ degree) / δ ^ degree
      let cutoff := max (allocatedSlicedGridHeightCutoff (G := G) B (R := R)
        (selected a).1 (selected a).2 (Nat.ceil ((1 : ℝ) / δ)))
        (denom * 2 ^ degree * Hchild ^ degree + 2 * denom)
      max (cutoff : ℝ)
        (uniformSpectrumAbsoluteCap (selected a).1.val 1 degree Ptail V V) ≤ Ctail)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)
    (u : integerBox physicalN) :
    let cap := (fixedSpatialOriginalForecastCap B (slice.slicedBlockEquiv true) s.hδslice : ℝ)
    let Cdecay := (((slice.path.Rbad * ∏ q : slice.path.primes,
      q.val ^ slice.path.prescribed q.val : ℕ) : ℝ) ^
      (modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) *
        modularRankChargeFactor m))
    ‖slice.target selected s.hBactive o bW hb originalpoly hmem s.κ u‖ ≤
      s.κ * cap * Ctail ^ Fintype.card A * (1 + Cdecay) := by
  sorry

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end
