-- Prove2me | Theorems.Thm_MaxCompForest_lemma_3_5
-- name    : MaxCompForest.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:41:11.008738+00:00
-- url     : https://prove2.me/theorems/f0fdba42-a7f2-4314-91b4-cce3877281fb
-- title:
--   Lemma 3.5 — physical mass-support optimizer
-- statement:
--   There are one machine and absolute constants $C,a,b$ with the following property. Let $H$ be a connected loopless edge-labelled multigraph with positive rational conductances $c_e$ and actual weighted degrees $d_v$, $1\le q<|V(H)|$, $\lambda_{q+1}(N_H)\ge\gamma$ for rational $0<\gamma\le1$, and let $\mathbf F=[\phi_v]\in\mathbb Q^{r\times V(H)}$, $0\le r\le q-1$, satisfy $\mathcal E_H(\phi)\le q$. Given rational $0<\varepsilon_0\le1$, an integer $k\ge1$ and an integer $0\le j\le\min\{k,|V(H)|-1\}$, the machine returns an actual labelled $j$-edge forest $F_{\mathrm{out}}$ with
--   $$
--   W_\phi(F_{\mathrm{out}})\ge\frac{1}{1+\varepsilon_0}\max_{\substack{F\text{ forest in }H\\|F|=j}}W_\phi(F),
--   $$
--   in at most $\lceil(Ckq/(\gamma\varepsilon_0))^{ak}(L_F+2)^b\rceil$ steps, where $L_F$ is the input length. For $j=0$ it returns the empty forest.
--
--   This is the terminal optimizer: it searches rounded partial trees with small retained supports, and returns a real forest of labelled edges.
--
--   Differences from the source:
--   - reading: “a deterministic algorithm … bit time” → one Mathlib multi-stack machine `TM2ComputableAux Sym Sym` on a fixed binary encoding; reason: the paper names no machine; a bit-operation algorithm and a multi-stack machine differ by a polynomial, which the time bound absorbs with changed absolute constants
--   - encoding: $L_F$ includes the actual degrees → the input word omits them; `deg` is computed from the conductances; reason: degrees are sums of the input conductances, of polynomially bounded length, so the two lengths are polynomially related
--   - encoding: $W_\phi(F_{\mathrm{out}})\ge\frac{1}{1+\varepsilon_0}\max_F W_\phi(F)$ → $W_\phi(F)\le(1+\varepsilon_0)W_\phi(F_{\mathrm{out}})$ for every forest $F$ with $j$ edges; reason: the same statement; the division is cleared and the family is finite and nonempty
--   - encoding: the algorithm is run under the theorem's hypotheses → behaviour outside the hypotheses is unconstrained, including non-halting; reason: the theorem assumes the promise; the machine is not asked to verify it
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Lemma 3.5, pp.22–23

import Mathlib
import Definitions.Def_MaxCompForest_RInst
import Definitions.Def_MaxCompForest_lam
import Definitions.Def_MaxCompForest_deg
import Definitions.Def_MaxCompForest_energy
import Definitions.Def_MaxCompForest_ratFeat
import Definitions.Def_MaxCompForest_covObj
import Definitions.Def_MaxCompForest_IsForest
import Definitions.Def_MaxCompForest_timeBound
import Definitions.Def_MaxCompForest_encOptIn
import Definitions.Def_MaxCompForest_encIndices
import Definitions.Def_CFLOutliers_OutputsWithin
import Definitions.Def_OnlineCRS_Combine_Sym
open EffResSparsify.ResistanceSketch
open OnlineCRS.Combine (Sym)
open CFLOutliers (OutputsWithin)

namespace MaxCompForest

/-- **Lemma 3.5 (Physical mass-support optimizer)**: one machine and absolute `C`, `a`, `b` before all instances;
time `⌈(Ckq/(γε₀))^(ak) (L_F + 2)^b⌉`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), pp.22–23.

**Formalization Note.** The degrees in `W_ϕ` are `deg I.graph`, computed from the conductances, and are not written
in the input (see `encOptIn`). The maximum over forests is written as a bound against each forest with `j` edges. -/
theorem lemma_3_5 :
    ∃ (M : Turing.TM2ComputableAux Sym Sym) (C a b : ℕ), 0 < C ∧
      ∀ (I : RInst) (q : ℕ) (γ : ℚ) (r : ℕ) (Ft : Fin r → Fin I.n → ℚ) (ε₀ : ℚ) (k j : ℕ),
        I.graph.IsConnected → 1 ≤ q → q < I.n → 0 < γ → γ ≤ 1 →
        (γ : ℝ) ≤ lam I.graph (deg I.graph) q → r + 1 ≤ q → energy I.graph (ratFeat Ft) ≤ q →
        0 < ε₀ → ε₀ ≤ 1 → 1 ≤ k → j ≤ k → j + 1 ≤ I.n →
        ∃ Fout : List (Fin I.m), Fout.Nodup ∧ Fout.length = j ∧
          IsForest I.graph Fout.toFinset ∧
          (∀ F : Finset (Fin I.m), IsForest I.graph F → F.card = j →
            covObj I.graph (deg I.graph) (ratFeat Ft) F ≤
              (1 + (ε₀ : ℝ)) * covObj I.graph (deg I.graph) (ratFeat Ft) Fout.toFinset) ∧
          OutputsWithin M (encOptIn I q γ r Ft ε₀ k j) (encIndices Fout)
            (timeBound C a b k q γ ε₀ (encOptIn I q γ r Ft ε₀ k j).length) := by sorry

end MaxCompForest
