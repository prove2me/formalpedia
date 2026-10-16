-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_actualFixedSpatialSlicedForecast_universal_native_source
-- name    : OAI.Erdos3.VectorPolynomial.exists_actualFixedSpatialSlicedForecast_universal_native_source
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-16T01:44:35.590696+00:00
-- url     : https://prove2.me/theorems/90cb9e3b-f214-46ea-b80b-5637cbb81739
-- title:
--   The sliced forecast target is approximated by a short sum of normalized twists
-- statement:
--   Fix: a natural number $m$; a finite type $G$; finite types $I_j$ ($j \in \mathrm{Fin}\,m$) and $n : \mathrm{Fin}\,m \to \mathbb N$; finite types $B_a$ for $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \le \mathbb R^{J_j}$ and bases $b_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`; reals $R_j, \sigma_j$, a `LayerSamplerScale` $S$ for $(B, U, b, R, \sigma)$ over $G$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities), and proofs $hR$, $h\sigma$ that $R_j > 0$ and $\sigma_j > 0$; a finite type $X$ with decidable equality; finite types $E_j$ (`Eout`); natural numbers $D_{\mathrm{mod}}$ and $L$; embeddings $\mathrm{spatial} : \mathrm{Fin}\,L \hookrightarrow G$, $\mathrm{kernel}_j : \mathrm{Fin}\,L \times \mathrm{Fin}(j+1) \hookrightarrow G$, and $\mathrm{block}_{j,a} : \mathrm{Fin}\,L \hookrightarrow B_{\langle j, a\rangle}$ for every axis $a$ of layer $j$ that is not short (`AllocatedDegreeActiveAxis short j`, where $\mathrm{short}$ is the predicate `allocatedShortAxis U b S.value`); a finite type $T_{\mathrm{sp}}$ and an equivalence $G \simeq X \oplus (X \oplus T_{\mathrm{sp}})$; reals $W_{\mathrm{sp}}, L_{\mathrm{sp}}$; $N : X \to \mathbb N$ (`physicalN`); reals $\tau, \delta_{\mathrm{slice}}$; a finite type $A$ and $\mathrm{selected} : A \to \Sigma_j\, \mathrm{Fin}(n_j)$. Let $s$ be an `ActualFixedSpatialForecastSetup B U b S Dmod selected τ δslice` (over $X$ and $E$; a structure bundling inequalities and real parameters, among them $s.P, s.P_{\mathrm{bad}}, s.P_{\mathrm{pres}}, s.\kappa$, $s.L \in \mathbb R_{\ge 0}$, $s.K \in \mathbb R_{\ge 0}$ with $R_j^{-1} \le s.K$, $s.\mathrm{forward} : \mathrm{Fin}\,m \to \mathbb R_{\ge 0}$ bounding the norms of the charts `normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)`, $s.\mathrm{radius} \in \mathbb R_{\ge 0}$, and proofs `s.hτ` of $\tau > 0$, `s.hδslice` of $\delta_{\mathrm{slice}} > 0$ and `s.hBactive` that $|B_a| \ge 4$ for every axis that is not short). Let $o_j$ be orthonormal bases of `euclideanSubspace (U j)` indexed by $I_j$; $bW_j$ $\mathbb Z$-bases, indexed by $E_j$, of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`; and $hb$ the statement that the $\mathbb Z$-span of $b_j$ is `projectedIntegerLattice (euclideanSubspace (U j))`. For $a \in A$ with $\mathrm{selected}(a) = (j_a, i_a)$ write $a^* = \langle j_a, \mathrm{inr}\ i_a\rangle$ and $H^{\mathrm{pr}} =$ `allocatedPrincipalSides B U b S`.
--
--   Let `slice` be an `ActualFixedSpatialSlicedForecastPath` over these data with parameters $(s.P, s.P_{\mathrm{bad}}, s.P_{\mathrm{pres}})$ (a structure bundling an `ActualFixedSpatialForecastPath` `slice.path` with a step, kernel data, and principal lengths, steps and starts). Let $T > 0$ be a natural number, $\delta > 0$ and $P$ reals, and $H_{\mathrm{child}}$ a natural number, such that for every $a \in A$ either $H^{\mathrm{pr}}_{(a^*, b_0, v_0)} < H_{\mathrm{child}}$ for some $b_0, v_0$, or [$\delta H^{\mathrm{pr}}_{(a^*, i, v)} \le$ `slice.principalLength` $(a^*, i, v)$ and `slice.principalStep` $(a^*, i, v) > 0$ for all $i, v$]. Assume $P \ge 1$, `scalarCubePrimitiveEnvelope Empty s.L 1 0 T` $\le P$ (a real defined by OpenAI), and `slice.principalStep` $(a^*, b_0, v) \cdot T \le P$ for all $a, b_0, v$. Let $C_{\mathrm{actual}}, \delta_{\mathrm{out}}, Q, N_t, V_t, C_t, H_t$ be reals and $L_t \in \mathbb R_{\ge 0}$ with $C_{\mathrm{actual}} \ge 0$, $C_t \ge 0$, $\delta_{\mathrm{out}} > 0$, $Q \ge 0$, and `forecastInactiveSlicedSiteNumerics B selected q Hchild δ P Cactual δout Q Nt Vt Ct Ht Lt` for every natural number $q$ with $0 < q \le T$ (a conjunction of numerical inequalities defined by OpenAI). Let $P_{\mathrm{tail}}, C_{\mathrm{tail}}$ be reals with $P_{\mathrm{tail}} \ge 1$, `scalarCubePrimitiveEnvelope Empty s.L 1 0 1` $\le P_{\mathrm{tail}}$, `slice.principalStep` $(a^*, b_0, v) \le P_{\mathrm{tail}}$ for all $a, b_0, v$, $C_{\mathrm{tail}} \ge 0$, and for every $a \in A$, with $\mathrm{degree} = j_a + 1$, $\mathrm{denom} =$ `inactiveDenominator (principalProfileSize (R j_a) |layerIntegerPrincipalSlots B j_a i_a|)` (here `inactiveDenominator γ` $= \max(1, \lceil 1/\gamma\rceil)$ and `principalProfileSize R b` $= R/(8(b+1))$), $\mathrm{torus} =$ `blockTorusFactor 0 degree |B a*| 1`, $V = \mathrm{torus} \cdot \mathrm{denom} \cdot 2^{\mathrm{degree}}/\delta^{\mathrm{degree}}$ and $\mathrm{cutoff} = \max(\mathrm{allocatedSlicedGridHeightCutoff}(B, j_a, i_a, \lceil 1/\delta\rceil),\ \mathrm{denom}\cdot 2^{\mathrm{degree}} H_{\mathrm{child}}^{\mathrm{degree}} + 2\,\mathrm{denom})$: $\max(\mathrm{cutoff}, \mathrm{uniformSpectrumAbsoluteCap}(j_a, 1, \mathrm{degree}, P_{\mathrm{tail}}, V, V)) \le C_{\mathrm{tail}}$.
--
--   Put $\mathrm{cap} =$ `fixedSpatialOriginalForecastCap B (slice.slicedBlockEquiv true) s.hδslice` and $\mathrm{lip} =$ `fixedSpatialOriginalForecastLip B (slice.slicedBlockEquiv false) (slice.slicedBlockEquiv true) s.hδslice` (nonnegative reals defined by OpenAI), $H = \mathrm{cap} + 1$, $L_{\mathrm{factor}} = (\mathrm{lip} + |A| L_t) \max(8/\tau, 1)$, $L_{\mathrm{coord}} = s.K \sum_j s.\mathrm{forward}_j |J_j|$, $L_{\mathrm{cut}} = \bigl(|\mathrm{LayerSamplerAxis}\ I\ n| \cdot c_0 / (2\, s.\mathrm{radius})\bigr) L_{\mathrm{coord}}$ with $c_0$ the constant `normalizedSiteCutoffBound`, $\mathrm{Out} = \Sigma_j$ `AllocatedCongruenceRankOutput X E short j`, and
--   $$C_{\mathrm{decay}} = \Bigl(R_{\mathrm{bad}} \prod_{p \in \mathrm{primes}} p^{\mathrm{prescribed}(p)}\Bigr)^{\mathrm{modularRankDecayExponent}(m,\ \mathrm{modularForecastRankConstant}(m, D_{\mathrm{mod}})) \cdot \mathrm{modularRankChargeFactor}(m)}$$
--   with $R_{\mathrm{bad}}$, $\mathrm{primes}$, $\mathrm{prescribed}$ the fields of `slice.path`, `modularForecastRankConstant s D` $= (D+2)(2^s s!)2^s$, `modularRankDecayExponent s C` $= C/(2^s s!)/2^s$ and `modularRankChargeFactor s` $= 4s(2^s s!)$.
--
--   Then for every real $P_{\mathrm{native}} \ge 0$ with $T V_t^{|A|} \le e^{P_{\mathrm{native}}}$ and $L_{\mathrm{factor}}, L_{\mathrm{coord}}, L_{\mathrm{cut}} \le e^{P_{\mathrm{native}}}$, there exist a finite type $\mathrm{Term}$, coefficients $\mathrm{coeff} : \mathrm{Term} \to \mathbb C$ and, for each term $t$, a `NormalizedPolynomialTwist X (Σ j, J j) c c c` $\mathrm{twist}_t$ with $c = e^{3P_{\mathrm{native}} + 3}$ (a structure bundling a modulus and a cover number at most $c$, a mask on $(\mathbb Z/\mathrm{modulus})^X$ of norm at most $1$, and a smooth function of norm at most $1$ that is $c$-Lipschitz), such that
--   $$\sum_t \|\mathrm{coeff}(t)\| \le s.\kappa \cdot 2H\, T^{|\mathrm{Out}| + 1} C_t^{|A|},$$
--   and for all vector polynomials $\mathrm{originalpoly}_j$ on $X$ with values in $\mathbb R^{J_j}$ and coefficients in $U_j$ (proof $hmem$), and every $u : X \to \mathbb Z$,
--   $$\Bigl\|\mathrm{slice.targetAt}(\mathrm{selected}, s.\mathrm{hBactive}, o, bW, hb, \mathrm{originalpoly}, hmem, s.\kappa, u) - \sum_t \mathrm{coeff}(t)\, \mathrm{twist}_t.\mathrm{eval}\bigl(N, \mathrm{slice.path.physicalPolynomial}(\mathrm{originalpoly}), u\bigr)\Bigr\| \le s.\kappa\, H \Bigl(C_{\mathrm{tail}}^{|A|} \frac{C_{\mathrm{decay}}}{T} + T^{|\mathrm{Out}|+1} \delta_{\mathrm{out}}\Bigr),$$
--   where `targetAt` is a complex number defined by OpenAI ($s.\kappa$ times a `forecastLawDensityPhysicalTarget` built from the slice's data), `twist.eval` is the complex value of the twist defined by OpenAI, and `slice.path.physicalPolynomial originalpoly` is $j \mapsto \mathrm{originalpoly}_j$ minus the constant `slice.path.center j`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_actualFixedSpatialSlicedForecast_universal_native_source` in `lean/OAI/Combinatorics/Progressions/Sampling/ActualSlicedForecastLateData.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B076` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ActualSlicedForecastLateData.lean#L651

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B076

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable {A : Type*} [Fintype A]

variable {Vact Out : Type*} [Fintype Vact] [DecidableEq Vact] [Fintype Out] [DecidableEq Out]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable {A : Type*} [Fintype A]

variable {Vact : Type*} [Fintype Vact] [DecidableEq Vact]
variable {X : Type*} [Fintype X]
variable {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)

end Erdos3.VectorPolynomial

end

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
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)

end Erdos3.VectorPolynomial

end

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
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))

namespace ActualFixedSpatialSlicedForecastPath

end ActualFixedSpatialSlicedForecastPath

theorem exists_actualFixedSpatialSlicedForecast_universal_native_source
    (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice s.P s.Pbad s.Ppres)
    (T : ℕ) (hT : 0 < T) (δ P : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U b S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ i v, δ * allocatedPrincipalSides B U b S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ ≤
        (slice.principalLength ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ : ℝ)) ∧
       (∀ i v, 0 < slice.principalStep ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩)))
    (hP : 1 ≤ P) (hprimitive : scalarCubePrimitiveEnvelope Empty s.L 1 0 T ≤ P)
    (hstride : ∀ a b0 v, ((slice.principalStep
      ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v⟩ * T : ℕ) : ℝ) ≤ P)
    (Cactual δout Q Nt Vt Ct Ht : ℝ) (Lt : ℝ≥0)
    (hCactual : 0 ≤ Cactual) (hCt : 0 ≤ Ct) (hδout : 0 < δout) (hQ : 0 ≤ Q)
    (hnumerics : ∀ q : ℕ, 0 < q → q ≤ T →
      forecastInactiveSlicedSiteNumerics (G := G) B (R := R) selected q Hchild
        δ P Cactual δout Q Nt Vt Ct Ht Lt)
    (Ptail Ctail : ℝ) (hPtail : 1 ≤ Ptail)
    (hsPtail : scalarCubePrimitiveEnvelope Empty s.L 1 0 1 ≤ Ptail)
    (hstrideTail : ∀ a b v,
      (slice.principalStep ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ) ≤ Ptail)
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
    :
    let cap := fixedSpatialOriginalForecastCap B (slice.slicedBlockEquiv true) s.hδslice
    let lip := fixedSpatialOriginalForecastLip B (slice.slicedBlockEquiv false)
      (slice.slicedBlockEquiv true) s.hδslice
    let H : ℝ := cap + 1
    let Lfactor := (lip + Fintype.card A * Lt) * max ⟨8 / τ, div_nonneg (by norm_num) s.hτ.le⟩ 1
    let Lcoord := s.K * ∑ j, s.forward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound /
      (2 * s.radius)) * Lcoord
    let Out := Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U b S.value))
    let Cdecay := (((slice.path.Rbad * ∏ p : slice.path.primes,
      p.val ^ slice.path.prescribed p.val : ℕ) : ℝ) ^
      (modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) * modularRankChargeFactor m))
    ∀ {Pnative : ℝ}, 0 ≤ Pnative →
      (T : ℝ) * Vt ^ Fintype.card A ≤ Real.exp Pnative →
      (Lfactor : ℝ) ≤ Real.exp Pnative → (Lcoord : ℝ) ≤ Real.exp Pnative →
      (Lcut : ℝ) ≤ Real.exp Pnative →
    ∃ (Term : Type) (_ : Fintype Term) (coeff : Term → ℂ)
      (twists : Term → NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp (3 * Pnative + 3)) (Real.exp (3 * Pnative + 3))
        ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩),
      (∑ t, ‖coeff t‖) ≤ s.κ * (2 * H * ((T : ℝ) ^ (Fintype.card Out + 1) * Ct ^ Fintype.card A)) ∧
      ∀ (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j) (u : X → ℤ),
        ‖slice.targetAt selected s.hBactive o bW hb originalpoly hmem s.κ u -
          ∑ t, coeff t * (twists t).eval physicalN
            (slice.path.physicalPolynomial originalpoly) u‖ ≤
          s.κ * (H * (Ctail ^ Fintype.card A * (Cdecay / T) +
            (T : ℝ) ^ (Fintype.card Out + 1) * δout)) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
