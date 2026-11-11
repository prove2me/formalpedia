-- Prove2me | Theorems.Thm_KAQROM_eq_4
-- name    : KAQROM.eq_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:35:08.693527+00:00
-- url     : https://prove2.me/theorems/4f731bfe-db6b-476c-8336-1d6a714e37df
-- title:
--   Display (4) — given $(\mathsf F_{m,h},T_A,T_B)$ the oracle is uniform on $\mathcal H(h,t_A,t_B)$ and independent of the residual state
-- statement:
--   In a protocol of Definition 3.10, all prefix queries are classical, so once $M=m$, $T_A=t_A$ and $T_B=t_B$ are fixed, the residual state of Alice and Bob is the same for every oracle consistent with $t_A$ and $t_B$. Hence, for every partial oracle $h$, whenever $\Pr[\mathsf F_{m,h},T_A=t_A,T_B=t_B]>0$,
--   $$
--   H\mid(\mathsf F_{m,h},T_A=t_A,T_B=t_B)\ \sim\ \mathrm{Unif}(\mathcal H(h,t_A,t_B)),
--   $$
--   and under this conditioning the residual state is independent of $H$: the conditional state of $(H,S_A,S_B)$ is $\mathrm{Unif}(\mathcal H(h,t_A,t_B))\otimes\sigma$ for one density operator $\sigma$ on $S_AS_B$.
--
--   This conditional-oracle identity is what lets the attack resample the oracle together with fresh prefix views (Lemma 5.12).
--
--   Differences from the source:
--   - encoding: a security parameter λ with inputs $1^\lambda$ → one fixed λ, $1^\lambda$ arguments dropped; reason: every statement of §5.2 is at one fixed λ with explicit constants
--   - generalization: $X=\{0,1\}^{n(\lambda)}$, $Y=\{0,1\}^{\ell(\lambda)}$ with $\ell(\lambda)\ge1$ → any finite type $X$ and any $\ell\in\mathbb N$, including $\ell=0$ (with $Y=\{0,1\}^\ell$ kept as bit strings, XOR as addition in $\mathbb Z_2^\ell$); reason: $n(\lambda)$, $\ell(\lambda)$ enter only through the sets $X$, $Y$ and no argument uses $\ell\ge1$; $X=\{0,1\}^n$, $\ell\ge1$ is an instance
--   - encoding: quantum oracle algorithms making at most $q$ queries, alternating oracle-independent operations with $U_H$ → exactly $q$ query rounds interleaved with arbitrary channels (Kraus families), then a measurement; reason: a query on the response state $|+\rangle^{\otimes\ell}$ is idle, so any algorithm pads to exactly $q$; parties are computationally unbounded (Stinespring)
--   - encoding: classical oracle access in the prefix (Definition 3.1); stages $A_i$, $B_i$ with residual registers → each stage is $D$ query steps and one message step, each a quantum instrument selected by the party's classical record (messages so far, own query–answer list, step index); a step with outcome none makes no query; one fixed register per party; reason: this is Definition 3.1's classical access (answers returned classically and recorded); idle steps and a large enough register pad any finite stage
--   - encoding: keys in $K_\lambda\cup\{\bot\}$ → `Option K` with ⊥ = `none`; reason: same values
--   - encoding: "$H\mid(\dots)\sim\mathrm{Unif}(\mathcal H(h,t_A,t_B))$; the residual state is independent of $H$" → the conditional state of $(H,S_A,S_B)$, block by block over $H$, equals $\mathrm{Unif}(\mathcal H(h,t_A,t_B))\otimes\sigma$ for a density operator $\sigma$; reason: the two clauses together are this product form
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), §5.2.1, display (4) and the sentence after it, p.33

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_KAQROM_Oracle
import Definitions.Def_KAQROM_Protocol
import Definitions.Def_KAQROM_Protocol_Omega

namespace KAQROM

/-- **Display (4) and the sentence after it** (§5.2.1, p.33). Once `M = m`, `T_A = t_A`,
`T_B = t_B` are fixed, whenever the conditioning event has positive probability,
`H | (F_{m,h}, T_A = t_A, T_B = t_B) ∼ Unif(ℋ(h, t_A, t_B))`, and under this conditioning the
residual state of Alice and Bob is independent of `H`: the conditional state of
`(H, S_A, S_B)` is `Unif(ℋ(h, t_A, t_B)) ⊗ σ` for one density operator `σ` on `S_A S_B`.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), §5.2.1, display (4), p.33.

**Formalization Note.** The conditional state is given block by block over the oracle values
`H` (`condPrefixState`); both clauses are the product form. -/
theorem eq_4 {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Msg K : Type} [Fintype Msg]
    [DecidableEq Msg] [Fintype K] (P : Protocol X ℓ Msg K) (m : Fin P.n → Msg) (h : PartialOracle X ℓ) (tA tB : Transcript X ℓ)
    (hpos : 0 < P.probFT m h tA tB) :
    ∃ σ : Matrix (P.RA × P.RB) (P.RA × P.RB) ℂ, WildeQIT.IsDensityOperator σ ∧
      ∀ H : Oracle X ℓ, P.condPrefixState m h tA tB H =
        (if H ∈ oraclesExt h [tA, tB] then (((oraclesExt h [tA, tB]).card : ℂ))⁻¹ else 0) • σ := by sorry

end KAQROM
