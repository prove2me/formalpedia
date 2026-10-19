-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_actualFixedSpatialSlicedForecastNumerics_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_actualFixedSpatialSlicedForecastNumerics_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T05:08:19.453121+00:00
-- url     : https://prove2.me/theorems/f7c10098-3ca4-4883-9de1-9d61c1bf4928
-- title:
--   Existence of sliced forecast numerics for an actual fixed spatial forecast setup, with explicit native, mass and cap logarithms
-- statement:
--   **Setting.** Let $m \in \mathbb{N}$; let $G$ be a finite type; let $I_j$ ($j \in \mathrm{Fin}\,m$) be finite types, $n : \mathrm{Fin}\,m \to \mathbb{N}$, and $B_a$ finite types indexed by the sampler axes $a$ in `LayerSamplerAxis I n`; let $J_j$ be finite types, $U_j \subseteq \mathbb{R}^{J_j}$ subspaces, and $b_j$ a basis, indexed by $\mathrm{Fin}(n_j)$, of the orthogonal complement of $U_j$; let $R, \sigma : \mathrm{Fin}\,m \to \mathbb{R}$ and $S$ a `LayerSamplerScale B U b R σ` (defined by OpenAI). Let $X$ be a finite type with decidable equality, $E^{\mathrm{out}}_j$ finite types, $A$ a finite type, $D_{\mathrm{mod}} \in \mathbb{N}$, $\mathrm{selected} : A \to \Sigma_{j} \mathrm{Fin}(n_j)$, and $\tau, \delta_{\mathrm{slice}}$ reals. Let $s$ be an `ActualFixedSpatialForecastSetup B U b S D_mod selected τ δ_slice` (a structure defined by OpenAI bundling the numerical parameters of a forecast setup; among its fields are reals $s.P$, $s.P_{\mathrm{cap}}$, $s.P_{\mathrm{bad}}$, $s.P_{\mathrm{pres}}$, $s.P_\kappa$, a nonnegative real $s.K$, a nonnegative real $s.\mathrm{radius}$, and $s.\mathrm{forward} : \mathrm{Fin}\,m \to \mathbb{R}_{\ge 0}$).
--
--   **Hypotheses.** Let $\delta$ be real, $H_{\mathrm{child}} \in \mathbb{N}$, and $\mathrm{kernelV}, P_{\mathrm{tail}}, D, p, v, w, v_{\mathrm{child}}, E, P_{\mathrm{spatial}}, P_{\mathrm{coord}}, P_{\mathrm{cut}}$ reals. Assume:
--   - $0 < \delta$, $0 \le \mathrm{kernelV}$, $1 \le P_{\mathrm{tail}}$, $s.P_{\mathrm{cap}} \le P_{\mathrm{tail}}$, $1 \le D$, $0 \le p$, $0 \le v$, $0 \le w$, $0 \le v_{\mathrm{child}}$, $0 \le E$, $0 \le P_{\mathrm{spatial}}$, $0 \le P_{\mathrm{coord}}$, $0 \le P_{\mathrm{cut}}$;
--   - $|A| \le D$, $P_{\mathrm{tail}} \le e^{p}$, $\delta^{-1} \le e^{w}$, $H_{\mathrm{child}} \le e^{v_{\mathrm{child}}}$;
--   - for every $a \in A$, writing $\mathrm{selected}(a) = (j_a, i_a)$: $R_{j_a} > 0$, $j_a + 1 \le D$, $|B_{(j_a, \mathrm{inr}\, i_a)}| \le D$, $R_{j_a} \le e^{v}$, $R_{j_a}^{-1} \le e^{v}$, and $|\texttt{BoundedCoefficientExponent}\ K\ (j_a + 1)| \le e^{v}$ with $K$ = `LayerSamplerVariables G I n B`;
--   - $\texttt{layerTailDegree}\ m + 1 \le D$, where `layerTailDegree m` $= m(2^{m+1} + 1)$;
--   - $\max(8/\tau, 1) \le e^{P_{\mathrm{spatial}}}$;
--   - $s.K \cdot \sum_j s.\mathrm{forward}_j\, |J_j| \le e^{P_{\mathrm{coord}}}$;
--   - $\bigl(|\texttt{LayerSamplerAxis I n}| \cdot \texttt{normalizedSiteCutoffBound} / (2\, s.\mathrm{radius})\bigr) \cdot \bigl(s.K \sum_j s.\mathrm{forward}_j\, |J_j|\bigr) \le e^{P_{\mathrm{cut}}}$ (computed in $\mathbb{R}_{\ge 0}$), where `normalizedSiteCutoffBound` $\ge 1$ is a constant chosen by OpenAI (the Lipschitz parameter of a smooth cutoff).
--
--   **Definitions** (all functions are explicit and defined by OpenAI):
--   - $P_{\mathrm{sm}} = \texttt{forecastOriginalSmoothBudget}\ m\ (s.P + (|X| + 1)\,\mathrm{kernelV})$, where `forecastOriginalSmoothBudget m P` $= (10m + 30)(P + 1)^2$;
--   - $\mathrm{tailLog} = \texttt{slicedFixedUniformSiteLog}\ m\ (p + \texttt{slicedFixedZeroGeometryLog}\ D\ v\ w\ 0\ v_{\mathrm{child}})\ 0$;
--   - $P_{\mathrm{in}} = D \cdot \mathrm{tailLog}$;
--   - $P_{\mathrm{dec}} = (s.P_{\mathrm{bad}} + s.P_{\mathrm{pres}}) \cdot (D_{\mathrm{mod}} + 2) \cdot \texttt{modularRankChargeFactor}\ m$, where `modularRankChargeFactor m` $= 4m \cdot 2^m \cdot m!$;
--   - $V = P_{\mathrm{in}} + P_{\mathrm{dec}} + (E + s.P_\kappa + P_{\mathrm{sm}}) + 3$;
--   - $E_{\mathrm{site}} = E + s.P_\kappa + P_{\mathrm{sm}} + 1 + (D_{\mathrm{mod}} + 1) V$;
--   - $p_{\mathrm{all}} = p + V + \texttt{slicedFixedZeroGeometryLog}\ D\ v\ w\ V\ v_{\mathrm{child}}$;
--   - $Q = \texttt{slicedFixedUniformSiteLog}\ m\ p_{\mathrm{all}}\ (\texttt{slicedFixedUniformAccuracyLog}\ m\ D\ p_{\mathrm{all}}\ E_{\mathrm{site}})$;
--   - $O = \texttt{siteExponentialOutputLog}\ 1\ Q = (4Q + 8) + 8Q + 18$;
--   - $P_{\mathrm{native}} = (V + D\,O) + (P_{\mathrm{sm}} + D + O + 1 + P_{\mathrm{spatial}}) + P_{\mathrm{coord}} + P_{\mathrm{cut}} + 1$;
--   - $P_{\mathrm{mass}} = P_{\mathrm{sm}} + (D_{\mathrm{mod}} + 1) V + D\,O + 1$;
--   - $P_{\mathrm{cap}}' = P_{\mathrm{sm}} + P_{\mathrm{in}} + P_{\mathrm{dec}} + 1$.
--
--   **Conclusion.** There exists $\nu$ of type `ActualFixedSpatialSlicedForecastNumerics s` (a structure defined by OpenAI recording a positive integer $T$ and real parameters, together with inequalities relating them to $s$) such that $\nu.\delta = \delta$, $\nu.H_{\mathrm{child}} = H_{\mathrm{child}}$, $\nu.v = \mathrm{kernelV}$, $\nu.P_{\mathrm{tail}} = P_{\mathrm{tail}}$, $\nu.E = E$, $\nu.P_{\mathrm{native}} = P_{\mathrm{native}}$, $\nu.\mathrm{massLog} = s.P_\kappa + P_{\mathrm{mass}}$, $\nu.\mathrm{capLog} = s.P_\kappa + P_{\mathrm{cap}}'$, $\nu.C_{\mathrm{tail}} = e^{\mathrm{tailLog}}$, $\nu.T \le e^{V}$, $0 \le \nu.\mathrm{massLog}$ and $0 \le \nu.\mathrm{capLog}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_actualFixedSpatialSlicedForecastNumerics_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_actualFixedSpatialSlicedForecastNumerics` (in `lean/OAI/Combinatorics/Progressions/Sampling/PreparedActualSlicedForecastSetup.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B196`, `OAIE3v2B301` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/PreparedActualSlicedForecastSetup.lean (declaration OAI.Erdos3.VectorPolynomial.exists_actualFixedSpatialSlicedForecastNumerics)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196
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
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type} [Fintype A]
variable {Dmod : ℕ} {selected : A → Σ j : Fin m, Fin (n j)}
variable {τ δslice : ℝ}

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)

theorem exists_actualFixedSpatialSlicedForecastNumerics_s2
    (δ : ℝ) (Hchild : ℕ) (kernelV Ptail D p v w vchild E Pspatial Pcoord Pcut : ℝ)
    (hδ : 0 < δ) (hk : 0 ≤ kernelV) (hPtail : 1 ≤ Ptail)
    (hprimitive : s.Pcap ≤ Ptail) (hD : 1 ≤ D) (hp : 0 ≤ p)
    (hv : 0 ≤ v) (hw : 0 ≤ w) (hvc : 0 ≤ vchild) (hE : 0 ≤ E)
    (hsp : 0 ≤ Pspatial) (hco : 0 ≤ Pcoord) (hcu : 0 ≤ Pcut)
    (hcard : (Fintype.card A : ℝ) ≤ D) (hPp : Ptail ≤ Real.exp p)
    (hδw : δ⁻¹ ≤ Real.exp w) (hchild : (Hchild : ℝ) ≤ Real.exp vchild)
    (hR : ∀ a, 0 < R (selected a).1)
    (hdegree : ∀ a, (((selected a).1.val + 1 : ℕ) : ℝ) ≤ D)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ D)
    (hb : ∀ a, (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩) : ℝ) ≤ D)
    (hRv : ∀ a, R (selected a).1 ≤ Real.exp v)
    (hRi : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp v)
    (hcoeff : ∀ a, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1)) : ℝ) ≤ Real.exp v)
    (hspatial : max (8 / τ) 1 ≤ Real.exp Pspatial)
    (hcoord : ((s.K * ∑ j, s.forward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp Pcoord)
    (hcut : (((Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound /
      (2 * s.radius)) * (s.K * ∑ j, s.forward j * Fintype.card (J j)) : ℝ≥0) : ℝ) ≤ Real.exp Pcut) :
    let Psm := forecastOriginalSmoothBudget m (s.P + (Fintype.card X + 1) * kernelV)
    let tailLog := slicedFixedUniformSiteLog m (p + slicedFixedZeroGeometryLog D v w 0 vchild) 0
    let Pin := D * tailLog
    let Pdec := (s.Pbad + s.Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
    let V := Pin + Pdec + (E + s.Pκ + Psm) + 3
    let Esite := E + s.Pκ + Psm + 1 + ((Dmod + 1 : ℕ) : ℝ) * V
    let pAll := p + V + slicedFixedZeroGeometryLog D v w V vchild
    let Q := slicedFixedUniformSiteLog m pAll (slicedFixedUniformAccuracyLog m D pAll Esite)
    let O := siteExponentialOutputLog 1 Q
    let Pnative := (V + D * O) + (Psm + D + O + 1 + Pspatial) + Pcoord + Pcut + 1
    let Pmass := Psm + ((Dmod + 1 : ℕ) : ℝ) * V + D * O + 1
    let Pcap := Psm + Pin + Pdec + 1
    ∃ nu : ActualFixedSpatialSlicedForecastNumerics s,
      nu.δ = δ ∧ nu.Hchild = Hchild ∧ nu.v = kernelV ∧ nu.Ptail = Ptail ∧ nu.E = E ∧
      nu.Pnative = Pnative ∧ nu.massLog = s.Pκ + Pmass ∧ nu.capLog = s.Pκ + Pcap ∧
      nu.Ctail = Real.exp tailLog ∧ (nu.T : ℝ) ≤ Real.exp V ∧
      0 ≤ nu.massLog ∧ 0 ≤ nu.capLog := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
