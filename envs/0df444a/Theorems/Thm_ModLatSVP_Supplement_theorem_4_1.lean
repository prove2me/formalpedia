-- Prove2me | Theorems.Thm_ModLatSVP_Supplement_theorem_4_1
-- name    : ModLatSVP.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:21:04.167754+00:00
-- url     : https://prove2.me/theorems/7d207e62-c177-4fdd-b29d-2860c77af774
-- title:
--   Theorem 4.1, p.23 — fixed module rank, $\mathrm{rd}(K)=d^{o(1)}$ — exact SVP, CVP and all closest vectors in polynomial space and time $\mathrm{poly}_n\cdot d^{d/(2e)+o(d)}$
-- statement:
--   Fix a module rank $n\ge1$. Let $\mathcal P$ be a family of number fields whose root discriminants satisfy $\rho=\mathrm{rd}(K)=d^{o(1)}$, $d=[K:\mathbb Q]$: for every $\delta>0$, $\mathrm{rd}(K)\le d^{\delta}$ for all members of large enough degree. For a rank-$n$ module $M\cong\mathbb Z^{N}$, $N=nd$, over a totally real or CM member $K$, given in the input model of §2.2, the following three problems can be solved deterministically in polynomial working space and in time
--
--   $$(\ell+1)^{k}\,d^{\,d/(2e)+g(d)},$$
--
--   where $\ell$ is the input length (including the target when there is one), $k$ depends only on $n$, and $g$ is a function with $g(d)/d\to0$ depending on the family:
--
--   1. exact SVP: output a shortest nonzero vector of $M$;
--   2. exact CVP: for every rational target $t$, output a closest vector of $M$ to $t$;
--   3. for every rational target $t$, output every closest vector of $M$ to $t$, each once.
--
--   This is the fixed-rank consequence of the SVP-oracle reductions of §4, with the oracle implemented by Kannan's algorithm.
--
--   **Formalization Note** The algorithms are TM2 machines with the base mission's conventions for time, working space and outputs. The machines and the degrees are chosen before the family, and $g$ after it.
--
--   Differences from the source:
--   - generalization: for a family of fields with ρ = d^{o(1)}, algorithms solving the three problems (machine and polynomial degree may depend on the family) → machines M_SVP, M_CVP, M_all and degrees k, k' chosen before the family P, only g chosen after P; reason: the paper's algorithms (oracle reductions with Kannan's algorithm) do not depend on the family; choosing them first implies the source's statement for each family
--   - reading: K ranges over a family of fields with ρ = rd(K) = d^{o(1)} → a predicate P on number fields with ∀ δ > 0, ∃ d_1, every member of degree ≥ d_1 has rd(K) ≤ [K:ℚ]^δ; reason: the standard meaning of a family with rd(K) = d^{o(1)}
--   - reading: poly_n(B, d, ℓ(t)) d^{d/(2e)+o(d)} → ⌊(ℓ+1)^k · d^{d/(2e) + g(d)}⌋ steps, k depending only on n, g : ℕ → ℝ with g(d)/d → 0; reason: B, d, ℓ(t) ≤ ℓ; o(d) as an explicit function, chosen after the family and before the instance
--   - reading: "can be solved deterministically in polynomial space" (no machine named) → deterministic TM2 machines, time SpikyCVP.RunsWithin, working space SpaceWithin bounded by (ℓ+1)^{k'}; reason: same model as the published goal Theorem 1.1
--   - encoding: exact CVP for every rational target; enumeration of all closest vectors → one machine outputting a closest vector; one outputting a duplicate-free list whose members are exactly the closest vectors; reason: the two tasks of the statement, outputs as in the published Theorem 3.5
--   - encoding: rank-n module in the input model of Section 2.2 → module input (d, c, S, G, A) of ℤ^N with RepresentsField, RepresentsModule, IsStar, N = n·d; reason: the base mission's input model
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), Theorem 4.1, p.23 (PDF p.23); input model §2.2, p.12

import Mathlib
import Definitions.Def_SpikyCVP_RunsWithin
import Definitions.Def_SpikyCVP_encInst
import Definitions.Def_ModLatSVP_IsStar
import Definitions.Def_ModLatSVP_RepresentsModule
import Definitions.Def_ModLatSVP_encModule
import Definitions.Def_ModLatSVP_IsShortest
import Definitions.Def_ModLatSVP_SpaceWithin

open NumberField Filter Topology

namespace ModLatSVP

namespace Supplement

/-- **Theorem 4.1, §4, p.23: SVP and CVP at fixed module rank.** Kim, Lee, Son, *Exact SVP and CVP in
Structured Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027 submission (manuscript sha256
e7151fad…): "Fix n ≥ 1. Let M be a rank-n module over a totally real or CM field K of degree d, in the
input model of Section 2.2. Suppose K ranges over a family of fields with root discriminant
ρ = rd(K) = d^{o(1)}. Exact SVP, exact CVP for every rational target, and enumeration of all closest
vectors can be solved deterministically in polynomial space and time poly_n(B, d, ℓ(t)) d^{d/(2e)+o(d)}.
Here poly_n denotes a polynomial whose degree may depend on the fixed rank n, and ℓ(t) = 0 for SVP."

Fix `n ≥ 1`. There are three TM2 machines `M_SVP`, `M_CVP`, `M_all` and degrees `k, k'` (depending only on
`n`) such that for every family `P` of number fields with `rd(K) = [K:ℚ]^{o(1)}` (for every `δ > 0`,
`rd(K) ≤ [K:ℚ]^δ` for all members of large enough degree) there is a function `g` with `g(d)/d → 0` such
that for every totally real or CM member `K` of `P` of degree `d` and every module input `(d, c, S, G, A)`
of a rank-`n` module `ℤ^N`, `N = n d` (`ℓ` bits; `ℓ` includes the target when there is one):
1. `M_SVP` outputs a shortest nonzero vector;
2. for every rational target `t`, `M_CVP` outputs one closest vector to `t`;
3. for every rational target `t`, `M_all` outputs the list of all closest vectors to `t`, each once;
each within `(ℓ+1)^k d^{d/(2e) + g(d)}` steps and working space `(ℓ+1)^{k'}`.

**Formalization Note.**
* Machine, working space and output conventions as in `ModLatSVP.theorem_1_1`; `poly_n(B, d, ℓ(t))` is
  `(ℓ+1)^k` with `k` depending only on `n` (`B, d, ℓ(t) ≤ ℓ`).
* The family is a predicate `P` on number fields; "`ρ = d^{o(1)}`" is: for every `δ > 0` there is `d₁`
  with `rd(K) ≤ [K:ℚ]^δ` for every member of degree at least `d₁`.
* `+o(d)` is an explicit `g : ℕ → ℝ` with `g(d)/d → 0`, chosen after the family (it may depend on it) and
  before the instance. The machines and `k, k'` are chosen before the family (the algorithms do not
  depend on it); this is stronger than the reading with the family fixed first. -/
theorem theorem_4_1 (n : ℕ) (hn : 1 ≤ n) :
    ∃ (Msvp Mcvp Mall : Turing.TM2ComputableAux Bool Bool) (k k' : ℕ),
      ∀ P : ∀ (K : Type) [Field K] [NumberField K], Prop,
        (∀ δ : ℝ, 0 < δ → ∃ d₁ : ℕ, ∀ (K : Type) [Field K] [NumberField K], P K →
          d₁ ≤ Module.finrank ℚ K → rd K ≤ (Module.finrank ℚ K : ℝ) ^ δ) →
        ∃ g : ℕ → ℝ, Tendsto (fun m : ℕ => g m / m) atTop (𝓝 0) ∧
          ∀ (K : Type) [Field K] [NumberField K] (τ : K ≃ₐ[ℚ] K) (d N : ℕ) (ω : Fin d → K)
            (c : Fin d → Fin d → Fin d → ℤ) (S : Matrix (Fin d) (Fin d) ℤ)
            (G : Matrix (Fin N) (Fin N) ℚ) (A : Fin d → Matrix (Fin N) (Fin N) ℤ),
            P K → (IsTotallyReal K ∨ IsCMField K) → IsStar K τ → RepresentsField K τ ω c S →
            RepresentsModule K τ ω G A → N = n * d →
            ((∃ x : Fin N → ℤ, IsShortest G x ∧
                SpikyCVP.RunsWithin Msvp (encModule d N c S G A) (encIntVec x)
                  ⌊(((encModule d N c S G A).length : ℝ) + 1) ^ k *
                    (d : ℝ) ^ ((d : ℝ) / (2 * Real.exp 1) + g d)⌋₊) ∧
              SpaceWithin Msvp (encModule d N c S G A) (((encModule d N c S G A).length + 1) ^ k')) ∧
            ∀ t : Fin N → ℚ,
              ((∃ x : Fin N → ℤ, IsClosest G t x ∧
                  SpikyCVP.RunsWithin Mcvp (encModule d N c S G A ++ SpikyCVP.encVec t) (encIntVec x)
                    ⌊(((encModule d N c S G A ++ SpikyCVP.encVec t).length : ℝ) + 1) ^ k *
                      (d : ℝ) ^ ((d : ℝ) / (2 * Real.exp 1) + g d)⌋₊) ∧
                SpaceWithin Mcvp (encModule d N c S G A ++ SpikyCVP.encVec t)
                  (((encModule d N c S G A ++ SpikyCVP.encVec t).length + 1) ^ k')) ∧
              ((∃ xs : List (Fin N → ℤ), xs.Nodup ∧ (∀ x, x ∈ xs ↔ IsClosest G t x) ∧
                  SpikyCVP.RunsWithin Mall (encModule d N c S G A ++ SpikyCVP.encVec t)
                    (xs.flatMap encIntVec)
                    ⌊(((encModule d N c S G A ++ SpikyCVP.encVec t).length : ℝ) + 1) ^ k *
                      (d : ℝ) ^ ((d : ℝ) / (2 * Real.exp 1) + g d)⌋₊) ∧
                SpaceWithin Mall (encModule d N c S G A ++ SpikyCVP.encVec t)
                  (((encModule d N c S G A ++ SpikyCVP.encVec t).length + 1) ^ k')) := by sorry

end Supplement

end ModLatSVP
